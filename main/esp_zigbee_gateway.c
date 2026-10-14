/*
 * SPDX-FileCopyrightText: 2021-2024 Espressif Systems (Shanghai) CO LTD
 *
 * SPDX-License-Identifier: LicenseRef-Included
 *
 * Zigbee Gateway Example
 *
 * This example code is in the Public Domain (or CC0 licensed, at your option.)
 *
 * Unless required by applicable law or agreed to in writing, this
 * software is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied.
 */
#include <fcntl.h>
#include <string.h>
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "driver/usb_serial_jtag.h"
#include "esp_coexist.h"
#include "esp_check.h"
#include "esp_log.h"
#include "esp_netif.h"
#include "esp_vfs_dev.h"
#include "esp_vfs_eventfd.h"
#include "esp_wifi.h"
#include "nvs_flash.h"
#include "protocol_examples_common.h"
#include "esp_zigbee_gateway.h"
#include "zb_config_platform.h"
#include "esp_heap_caps.h"
#include "esp_random.h"

#include "esp_http_server.h"
#include <stdio.h>
#include "esp_timer.h"
#include "zboss_api_buf.h"

static void format_uptime(char *buffer, size_t size)
{
    uint64_t ms = (uint64_t)esp_timer_get_time() / 1000ULL;

    snprintf(buffer, size, "%02llu:%02llu:%02llu.%03llu",
             (unsigned long long)(ms / 3600000ULL),
             (unsigned long long)((ms / 60000ULL) % 60ULL),
             (unsigned long long)((ms / 1000ULL) % 60ULL),
             (unsigned long long)(ms % 1000ULL));
}

#define LOGI_TIME(format, ...) do { \
    char timestamp[24]; \
    format_uptime(timestamp, sizeof(timestamp)); \
    ESP_LOGI(TAG, "[%s] " format, timestamp, ##__VA_ARGS__); \
} while (0)

#define LOGW_TIME(format, ...) do { \
    char timestamp[24]; \
    format_uptime(timestamp, sizeof(timestamp)); \
    ESP_LOGW(TAG, "[%s] " format, timestamp, ##__VA_ARGS__); \
} while (0)

#define LOGE_TIME(format, ...) do { \
    char timestamp[24]; \
    format_uptime(timestamp, sizeof(timestamp)); \
    ESP_LOGE(TAG, "[%s] " format, timestamp, ##__VA_ARGS__); \
} while (0)

static const char *TAG = "ESP-ZB-GW";

static esp_zb_ieee_addr_t aqara_ieee_addr;
static bool w100_reporting_started;
static uint16_t w100_short_addr;
static uint8_t w100_pmtsd_counter;

typedef struct {
    uint8_t p;
    uint8_t m;
    float t;
    uint8_t s;
    uint8_t d;
} w100_pmtsd_state_t;

typedef struct {
    uint16_t short_addr;
    uint8_t endpoint;
} w100_sync_args_t;

static w100_pmtsd_state_t w100_pmtsd_state = {
    .p = 0, .m = 1, .t = 22.0f, .s = 2, .d = 0
};

typedef struct {
    uint8_t s;
} w100_fan_display_args_t;

static portMUX_TYPE w100_pmtsd_mux = portMUX_INITIALIZER_UNLOCKED;

static void pmtsd_send_console_line(uint16_t short_addr, uint8_t endpoint,
                                    const char *line, size_t len);
static bool w100_store_pmtsd(const w100_pmtsd_state_t *state);
static bool w100_parse_pmtsd(const char *text, size_t len,
                             w100_pmtsd_state_t *state);
static void w100_schedule_fan_display(uint8_t s);

static float temperatura_curenta = 0.0;
static float setpoint_temperatura = 22.0f;
static uint16_t umiditate_curenta = 0;
static enum { INIT, RUNNING, STOPPED } centrala_pornita = INIT;

#define MAX_TRACKED_DEVICES 16
// Accessed from Zigbee signal/callback handlers.
static uint16_t tracked_devices[MAX_TRACKED_DEVICES];
static size_t tracked_device_count;

static bool aqara_attr_discovery_started;
static bool w100_activation_started;
static bool w100_read_started;

static void task_w100_fan_display(void *arg)
{
    w100_fan_display_args_t *args = arg;
    uint8_t s = args->s;
    vPortFree(args);

    w100_pmtsd_state_t state;
    portENTER_CRITICAL(&w100_pmtsd_mux);
    state = w100_pmtsd_state;
    portEXIT_CRITICAL(&w100_pmtsd_mux);

    state.s = s;

    char text[43];
    int len = snprintf(text, sizeof(text), "P%u_M%u_T%.1f_S%u_D%u",
                       state.p, state.m, (double)state.t, state.s, state.d);

    if (len > 0 && len < (int)sizeof(text)) {
        pmtsd_send_console_line(w100_short_addr, 1, text, (size_t)len);
    } else {
        LOGE_TIME("[W100] Nu s-a putut forma PMTSD pentru S%u", s);
    }

    vTaskDelete(NULL);
}

static void w100_schedule_fan_display(uint8_t s)
{
    w100_fan_display_args_t *args = pvPortMalloc(sizeof(*args));
    if (args == NULL) {
        LOGE_TIME("[W100] Memorie insuficientă pentru schimbarea S%u", s);
        return;
    }

    args->s = s;
    if (xTaskCreate(task_w100_fan_display, "w100_fan_display",
                    3072, args, 4, NULL) != pdPASS) {
        vPortFree(args);
        LOGE_TIME("[W100] Nu s-a putut porni task-ul pentru S%u", s);
    }
}

static void task_discover_aqara_attributes(void *arg)
{
    uint16_t short_addr = (uint16_t)(uintptr_t)arg;
    esp_zb_zcl_disc_attr_cmd_t cmd = {0};

    cmd.zcl_basic_cmd.dst_addr_u.addr_short = short_addr;
    cmd.zcl_basic_cmd.dst_endpoint = 1;
    cmd.zcl_basic_cmd.src_endpoint = ESP_ZB_GATEWAY_ENDPOINT;
    cmd.address_mode = ESP_ZB_APS_ADDR_MODE_16_ENDP_PRESENT;
    cmd.cluster_id = 0xFCC0;
    cmd.direction = 0; // Client-to-server
    cmd.start_attr_id = 0x0000;
    cmd.max_attr_number = 0xFF;

    esp_zb_lock_acquire(portMAX_DELAY);
    uint8_t tsn = esp_zb_zcl_disc_attr_cmd_req(&cmd);
    esp_zb_lock_release();

    LOGI_TIME("[FCC0 DISC] cerere trimisa catre 0x%04hx EP 1 TSN=%u",
              short_addr, (unsigned)tsn);
    vTaskDelete(NULL);
}

static bool device_is_tracked(uint16_t short_addr)
{
    for (size_t i = 0; i < tracked_device_count; i++) {
        if (tracked_devices[i] == short_addr) {
            return true;
        }
    }
    return false;
}

static bool track_device(uint16_t short_addr)
{
    if (device_is_tracked(short_addr)) {
        return false;
    }

    if (tracked_device_count >= MAX_TRACKED_DEVICES) {
        LOGE_TIME("Device registry full; cannot track 0x%04hx", short_addr);
        return false;
    }

    tracked_devices[tracked_device_count++] = short_addr;
    return true;
}

static void untrack_device(uint16_t short_addr)
{
    for (size_t i = 0; i < tracked_device_count; i++) {
        if (tracked_devices[i] == short_addr) {
            tracked_devices[i] = tracked_devices[--tracked_device_count];
            return;
        }
    }
}

/* Logica locală de decizie a termostatului */
void ruleaza_logica_termostat(void)
{
    float toleranta = 0.2; // Histerezis de 0.2 grade pentru protecția centralei
    
    LOGW_TIME("[TERMOSTAT LOCAL] Setpoint = %.1f °C, Ambient = %.1f °C",
              setpoint_temperatura, temperatura_curenta);
    
    if (temperatura_curenta < (setpoint_temperatura - toleranta)
        && centrala_pornita != RUNNING) {
        centrala_pornita = RUNNING;
        LOGE_TIME("[CENTRALA] ON; W100 fan display S3");
        w100_schedule_fan_display(3);

        // TODO: Aici vom pune comanda Zigbee către relee în pasul următor

    } 
    else if (temperatura_curenta >= (setpoint_temperatura + toleranta)
             && centrala_pornita != STOPPED) {
        centrala_pornita = STOPPED;
        LOGE_TIME("[CENTRALA] OFF; W100 fan display S4");
        w100_schedule_fan_display(4);
        // TODO: Aici vom pune comanda Zigbee către relee în pasul următor
    }
}

void ruleaza_logica_umiditate(void) {
    LOGW_TIME("[UMIDITATE] %d %%", umiditate_curenta);
}

static void w100_log_frame(const char *name, const uint8_t *frame, size_t len)
{
    char hex[2 * 64 + 1];
    if (len > 64) {
        LOGW_TIME("[W100 FRAME] %s prea lung: %u", name, (unsigned)len);
        return;
    }

    for (size_t i = 0; i < len; i++) {
        snprintf(&hex[2 * i], sizeof(hex) - 2 * i, "%02x", frame[i]);
    }
    hex[2 * len] = '\0';
    LOGI_TIME("[W100 FRAME] %s len=%u %s", name, (unsigned)len, hex);
}

void trimite_setpoint_catre_aqara(uint16_t short_addr, uint8_t endpoint,
                                  float setpoint_val)
{
    // W100 acceptă setpoint-uri între 5 și 30 °C, în pași de 0,5 °C.
    if (setpoint_val < 5.0f || setpoint_val > 30.0f) {
        LOGW_TIME("[W100] Setpoint în afara intervalului: %.1f °C",
                  setpoint_val);
        return;
    }

    int tenths = (int)(setpoint_val * 10.0f + 0.5f);
    if (tenths % 5 != 0) {
        LOGW_TIME("[W100] Setpoint-ul trebuie să fie în pași de 0,5 °C");
        return;
    }

    w100_pmtsd_state_t state;
    portENTER_CRITICAL(&w100_pmtsd_mux);
    state = w100_pmtsd_state;
    portEXIT_CRITICAL(&w100_pmtsd_mux);
    state.t = setpoint_val;

    char text[43];
    int len = snprintf(text, sizeof(text), "P%u_M%u_T%.1f_S%u_D%u",
                       state.p, state.m, (double)state.t, state.s, state.d);

    if (len <= 0 || len >= (int)sizeof(text)) {
        LOGE_TIME("[W100] Eroare la formarea PMTSD");
        return;
    }

    pmtsd_send_console_line(short_addr, endpoint, text, (size_t)len);
}

static void task_w100_sync_reply(void *arg)
{
    w100_sync_args_t *args = arg;
    uint16_t short_addr = args->short_addr;
    uint8_t endpoint = args->endpoint;
    vPortFree(args);

    w100_pmtsd_state_t state;
    portENTER_CRITICAL(&w100_pmtsd_mux);
    state = w100_pmtsd_state;
    portEXIT_CRITICAL(&w100_pmtsd_mux);

    char text[43];
    int len = snprintf(text, sizeof(text), "P%u_M%u_T%.1f_S%u_D%u",
                       state.p, state.m, (double)state.t, state.s, state.d);

    if (len <= 0 || len >= (int)sizeof(text)) {
        LOGE_TIME("[W100 SYNC] Nu s-a putut forma PMTSD-ul memorat");
    } else {
        LOGI_TIME("[W100 SYNC] răspund cu starea memorată: %s", text);
        pmtsd_send_console_line(short_addr, endpoint, text, (size_t)len);
    }

    (void)short_addr;
    (void)endpoint;
    vTaskDelete(NULL);
}

static uint8_t w100_write_octet_frame(uint16_t short_addr, uint8_t endpoint,
                                      const uint8_t *frame, size_t frame_len)
{
    if (frame == NULL || frame_len == 0 || frame_len > 64) {
        LOGE_TIME("[W100] Cadru invalid, lungime=%u", (unsigned)frame_len);
        return 0;
    }

    // ESP-Zigbee cere lungimea octet string-ului în primul octet.
    uint8_t value[65];
    value[0] = (uint8_t)frame_len;
    memcpy(&value[1], frame, frame_len);

    esp_zb_zcl_attribute_t attr = {0};
    attr.id = 0xFFF2;
    attr.data.type = ESP_ZB_ZCL_ATTR_TYPE_OCTET_STRING;
    attr.data.size = (uint16_t)(frame_len + 1);
    attr.data.value = value;

    esp_zb_zcl_write_attr_cmd_t cmd = {0};
    cmd.zcl_basic_cmd.dst_addr_u.addr_short = short_addr;
    cmd.zcl_basic_cmd.dst_endpoint = endpoint;
    cmd.zcl_basic_cmd.src_endpoint = ESP_ZB_GATEWAY_ENDPOINT;
    cmd.address_mode = ESP_ZB_APS_ADDR_MODE_16_ENDP_PRESENT;
    cmd.clusterID = 0xFCC0;
    cmd.manuf_specific = 1;
    cmd.direction = 0;
    cmd.dis_default_resp = 1;
    cmd.manuf_code = 0x115F;
    cmd.attr_number = 1;
    cmd.attr_field = &attr;

    esp_zb_lock_acquire(portMAX_DELAY);
    uint8_t tsn = esp_zb_zcl_write_attr_cmd_req(&cmd);
    esp_zb_lock_release();
    return tsn;
}

static void task_w100_activate_and_setpoint(void *arg)
{
    uint16_t short_addr = (uint16_t)(uintptr_t)arg;

    const uint8_t prefix[] = {0xaa, 0x71, 0x32, 0x44, 0x00, 0x00};
    const uint8_t zcl_header[] = {0x02, 0x41, 0x2f, 0x68, 0x91};
    const uint8_t tail[] = {
        0x08, 0x00, 0x08, 0x44, 0x15, 0x0a, 0x01, 0x09,
        0xe7, 0xa9, 0xba, 0xe8, 0xb0, 0x83, 0xe5, 0x8a, 0x9f,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x01, 0x2a, 0x40
    };
    const uint8_t separator[] = {0x00, 0x00};
    const uint8_t hub_id[] = {0x54, 0xef, 0x44, 0x80, 0x71, 0x1a};

    uint8_t frame[64];
    size_t pos = 0;

    memcpy(&frame[pos], prefix, sizeof(prefix));
    pos += sizeof(prefix);
    frame[4] = (uint8_t)esp_random();
    frame[5] = (uint8_t)esp_random();

    memcpy(&frame[pos], zcl_header, sizeof(zcl_header));
    pos += sizeof(zcl_header);
    frame[pos++] = (uint8_t)esp_random(); // messageId
    frame[pos++] = (uint8_t)esp_random(); // messageId
    frame[pos++] = 0x18;                  // control

    // IEEE-ul W100 în ordinea canonică folosită de converter.
    for (int i = 7; i >= 0; --i) {
        frame[pos++] = aqara_ieee_addr[i];
    }

    memcpy(&frame[pos], separator, sizeof(separator));
    pos += sizeof(separator);
    memcpy(&frame[pos], hub_id, sizeof(hub_id));
    pos += sizeof(hub_id);
    memcpy(&frame[pos], tail, sizeof(tail));
    pos += sizeof(tail);

    LOGI_TIME("[W100] trimit cadrul ON, lungime=%u", (unsigned)pos);
    w100_log_frame("ON", frame, pos);
    uint8_t tsn = w100_write_octet_frame(short_addr, 1, frame, pos);
    LOGI_TIME("[W100] cerere thermostat_mode=ON trimisă, TSN=%u",
              (unsigned)tsn);

    vTaskDelay(pdMS_TO_TICKS(500));
    trimite_setpoint_catre_aqara(short_addr, 1, setpoint_temperatura);

    vTaskDelete(NULL);
}

static void on_bind_resp(esp_zb_zdp_status_t status, void *user_ctx)
{
    LOGI_TIME("[BIND] cluster=0x%04x status=0x%02x",
              (unsigned)(uintptr_t)user_ctx, (unsigned)status);
}

static void task_configure_w100_setpoint_reporting(void *arg)
{
    uint16_t short_addr = (uint16_t)(uintptr_t)arg;
    esp_zb_ieee_addr_t coordinator_ieee;
    esp_zb_get_long_address(coordinator_ieee);

    vTaskDelay(pdMS_TO_TICKS(7000));

    // Binding pentru rapoartele trimise nesolicitat către coordinator.
    const uint16_t clusters[] = {0xFCC0, 0x0402, 0x0405};
    for (size_t i = 0; i < sizeof(clusters) / sizeof(clusters[0]); i++) {
        esp_zb_zdo_bind_req_param_t bind = {0};
        memcpy(bind.src_address, aqara_ieee_addr, sizeof(bind.src_address));
        bind.src_endp = 1;
        bind.cluster_id = clusters[i];
        bind.dst_addr_mode = ESP_ZB_ZDO_BIND_DST_ADDR_MODE_64_BIT_EXTENDED;
        memcpy(bind.dst_address_u.addr_long, coordinator_ieee,
               sizeof(coordinator_ieee));
        bind.dst_endp = ESP_ZB_GATEWAY_ENDPOINT;
        bind.req_dst_addr = short_addr;

        esp_zb_lock_acquire(portMAX_DELAY);
        esp_zb_zdo_device_bind_req(&bind, on_bind_resp,
                                   (void *)(uintptr_t)clusters[i]);
        esp_zb_lock_release();
        vTaskDelay(pdMS_TO_TICKS(150));
    }

    vTaskDelay(pdMS_TO_TICKS(1500));

    int16_t temperature_change = 10;  // 0.10 °C; cluster 0x0402
    uint16_t humidity_change = 100;   // 1.00 %; cluster 0x0405

    struct {
        uint16_t cluster;
        uint16_t attribute;
        uint8_t type;
        void *change;
        bool manufacturer_specific;
    } reports[] = {
        {0xFCC0, 0xFFF2, ESP_ZB_ZCL_ATTR_TYPE_OCTET_STRING, NULL, true},
        {0x0402, 0x0000, 0x29, &temperature_change, false},
        {0x0405, 0x0000, 0x21, &humidity_change, false},
    };

    for (size_t i = 0; i < sizeof(reports) / sizeof(reports[0]); i++) {
        esp_zb_zcl_config_report_record_t record = {
            .direction = ESP_ZB_ZCL_REPORT_DIRECTION_SEND,
            .attributeID = reports[i].attribute,
            .attrType = reports[i].type,
            .min_interval = 10,
            .max_interval = 60,
            .reportable_change = reports[i].change,
        };

        esp_zb_zcl_config_report_cmd_t cmd = {0};
        cmd.zcl_basic_cmd.dst_addr_u.addr_short = short_addr;
        cmd.zcl_basic_cmd.dst_endpoint = 1;
        cmd.zcl_basic_cmd.src_endpoint = ESP_ZB_GATEWAY_ENDPOINT;
        cmd.address_mode = ESP_ZB_APS_ADDR_MODE_16_ENDP_PRESENT;
        cmd.clusterID = reports[i].cluster;
        cmd.direction = 0;
        cmd.manuf_specific = reports[i].manufacturer_specific;
        cmd.manuf_code = reports[i].manufacturer_specific ? 0x115F : 0;
        cmd.record_number = 1;
        cmd.record_field = &record;

        esp_zb_lock_acquire(portMAX_DELAY);
        uint8_t tsn = esp_zb_zcl_config_report_cmd_req(&cmd);
        esp_zb_lock_release();

        LOGI_TIME("[REPORT CFG TX] EP=1 cluster=0x%04hx attr=0x%04hx "
                  "min=10 max=60 TSN=%u",
                  reports[i].cluster, reports[i].attribute, (unsigned)tsn);
        vTaskDelay(pdMS_TO_TICKS(200));
    }

    vTaskDelete(NULL);
}

static void task_w100_read_thermostat_setpoint(void *arg)
{
    uint16_t short_addr = (uint16_t)(uintptr_t)arg;
    uint16_t attr_id = 0x0055;

    vTaskDelay(pdMS_TO_TICKS(8000));

    esp_zb_zcl_read_attr_cmd_t cmd = {0};
    cmd.zcl_basic_cmd.dst_addr_u.addr_short = short_addr;
    cmd.zcl_basic_cmd.dst_endpoint = 1;
    cmd.zcl_basic_cmd.src_endpoint = ESP_ZB_GATEWAY_ENDPOINT;
    cmd.address_mode = ESP_ZB_APS_ADDR_MODE_16_ENDP_PRESENT;
    cmd.clusterID = 0xFCC0;
    cmd.attr_number = 1;
    cmd.attr_field = &attr_id;
    cmd.manuf_specific = 1;
    cmd.manuf_code = 0x115F;

    esp_zb_lock_acquire(portMAX_DELAY);
    uint8_t tsn = esp_zb_zcl_read_attr_cmd_req(&cmd);
    esp_zb_lock_release();

    LOGI_TIME("[W100 ATTR READ TX] cluster=0xFCC0 attr=0x0055 "
              "manuf=0x115F addr=0x%04hx EP=1 TSN=%u",
              short_addr, (unsigned)tsn);
    vTaskDelete(NULL);
}

static void on_simple_desc_resp(esp_zb_zdp_status_t zdo_status,
                                esp_zb_af_simple_desc_1_1_t *desc,
                                void *user_ctx)
{
    uintptr_t ctx = (uintptr_t)user_ctx;
    uint16_t short_addr = (uint16_t)(ctx >> 8);
    uint8_t endpoint = (uint8_t)ctx;

    if (zdo_status != ESP_ZB_ZDP_STATUS_SUCCESS || desc == NULL) {
        LOGW_TIME("[SIMPLE DESC] 0x%04hx EP %u esuat: status=0x%02x",
                  short_addr, endpoint, zdo_status);
        return;
    }

    bool has_temperature = false;
    bool has_humidity = false;
    bool has_aqara = false;

    for (uint8_t i = 0; i < desc->app_input_cluster_count; i++) {
        uint16_t cluster = desc->app_cluster_list[i];
        has_temperature |= cluster == ESP_ZB_ZCL_CLUSTER_ID_TEMP_MEASUREMENT;
        has_humidity |= cluster == ESP_ZB_ZCL_CLUSTER_ID_REL_HUMIDITY_MEASUREMENT;
        has_aqara |= cluster == 0xFCC0;
    }

    if (desc->endpoint == 1 && has_aqara &&
        !aqara_attr_discovery_started) {
        aqara_attr_discovery_started = true;
        if (xTaskCreate(task_discover_aqara_attributes, "fcc0_discover",
                        3072, (void *)(uintptr_t)short_addr, 5, NULL) != pdPASS) {
            aqara_attr_discovery_started = false;
            LOGE_TIME("Nu s-a putut porni descoperirea atributelor FCC0");
        }
    }
    
    if (desc->endpoint == 1 && has_aqara &&
        !w100_activation_started) {
        w100_short_addr = short_addr;
        w100_activation_started = true;
        if (xTaskCreate(task_w100_activate_and_setpoint, "w100_activate",
                        4096, (void *)(uintptr_t)short_addr, 5, NULL) != pdPASS) {
            w100_activation_started = false;
            LOGE_TIME("[W100] Nu s-a putut porni task-ul de activare");
        }
    }

    LOGI_TIME("[SIMPLE DESC] 0x%04hx EP %u profile=0x%04hx device=0x%04hx "
              "input=%u output=%u",
              short_addr, desc->endpoint, desc->app_profile_id,
              desc->app_device_id, desc->app_input_cluster_count,
              desc->app_output_cluster_count);

    for (uint8_t i = 0; i < desc->app_input_cluster_count; i++) {
        LOGI_TIME("[SIMPLE DESC] EP %u INPUT cluster=0x%04hx",
                  desc->endpoint, desc->app_cluster_list[i]);
    }

    for (uint8_t i = 0; i < desc->app_output_cluster_count; i++) {
        uint8_t index = desc->app_input_cluster_count + i;
        LOGI_TIME("[SIMPLE DESC] EP %u OUTPUT cluster=0x%04hx",
                  desc->endpoint, desc->app_cluster_list[index]);
    }

    if (desc->endpoint == 1 && has_aqara && !w100_read_started) {
        w100_read_started = true;
        if (xTaskCreate(task_w100_read_thermostat_setpoint,
                        "w100_native_read", 3072,
                        (void *)(uintptr_t)short_addr, 4, NULL) != pdPASS) {
            w100_read_started = false;
            LOGE_TIME("[W100 NATIVE READ] Nu s-a putut porni testul");
        }
    }

    if (desc->endpoint == 1 && has_aqara && !w100_reporting_started) {
        w100_reporting_started = true;
        if (xTaskCreate(task_configure_w100_setpoint_reporting,
                        "w100_report_cfg", 3072,
                        (void *)(uintptr_t)short_addr, 4, NULL) != pdPASS) {
            w100_reporting_started = false;
            LOGE_TIME("[W100 REPORT CFG] Nu s-a putut porni task-ul");
        }
    }
}

static void on_active_ep_resp(esp_zb_zdp_status_t zdo_status,
                              uint8_t ep_count, uint8_t *ep_id_list,
                              void *user_ctx)
{
    uint16_t short_addr = (uint16_t)(uintptr_t)user_ctx;

    if (zdo_status != ESP_ZB_ZDP_STATUS_SUCCESS ||
        (ep_count > 0 && ep_id_list == NULL)) {
        LOGE_TIME("Active EP esuat pentru 0x%04hx: status=0x%02x",
                  short_addr, zdo_status);
        untrack_device(short_addr);
        return;
    }

    LOGI_TIME("Device 0x%04hx: %u endpoint-uri active",
              short_addr, ep_count);

    for (uint8_t i = 0; i < ep_count; i++) {
        uint8_t endpoint = ep_id_list[i];
        esp_zb_zdo_simple_desc_req_param_t req = {
            .addr_of_interest = short_addr,
            .endpoint = endpoint,
        };
        void *ctx = (void *)(((uintptr_t)short_addr << 8) | endpoint);

        LOGI_TIME("Cer Simple Descriptor pentru 0x%04hx EP %u",
                  short_addr, endpoint);
        esp_zb_zdo_simple_desc_req(&req, on_simple_desc_resp, ctx);
    }

    // Raportarea nesolicitată este activă; polling-ul nu mai este pornit.
    // if (xTaskCreate(task_interogare_temperatura, "polling_temp", 3072,
    //                 (void *)(uintptr_t)short_addr, 5, NULL) != pdPASS) {
    //     LOGE_TIME("Nu s-a putut crea task-ul de polling");
    //     untrack_device(short_addr);
    // }
}

static void task_configurare_aqara(void *pvParameters)
{
    uint16_t short_addr = (uint16_t)(uintptr_t)pvParameters;
    vTaskDelay(pdMS_TO_TICKS(1000));

    esp_zb_zdo_active_ep_req_param_t active_ep_req = {0};
    active_ep_req.addr_of_interest = short_addr; 
    
    esp_zb_lock_acquire(portMAX_DELAY);
    esp_zb_zdo_active_ep_req(
        &active_ep_req,
        (esp_zb_zdo_active_ep_callback_t)on_active_ep_resp,
        (void *)(uintptr_t)short_addr);
    esp_zb_lock_release();

    vTaskDelete(NULL);
}


void esp_zb_app_signal_handler(esp_zb_app_signal_t *signal_struct)
{
    uint32_t *p_sg_p       = signal_struct->p_app_signal;
    esp_err_t err_status = signal_struct->esp_err_status;
    esp_zb_app_signal_type_t sig_type = *p_sg_p;
    esp_zb_zdo_signal_device_annce_params_t *dev_annce_params = NULL;

    switch (sig_type) {
    case ESP_ZB_ZDO_SIGNAL_SKIP_STARTUP:
        esp_zb_bdb_start_top_level_commissioning(ESP_ZB_BDB_MODE_INITIALIZATION);
        break;
    case ESP_ZB_BDB_SIGNAL_DEVICE_FIRST_START:
    case ESP_ZB_BDB_SIGNAL_DEVICE_REBOOT:
        LOGI_TIME("Zigbee startup signal %lu, status=%s",
                  (unsigned long)sig_type, esp_err_to_name(err_status));
        if (err_status == ESP_OK) {
            if (esp_zb_bdb_is_factory_new()) {
                LOGI_TIME("Coordinator nou: pornesc network formation");
                esp_zb_bdb_start_top_level_commissioning(ESP_ZB_BDB_MODE_NETWORK_FORMATION);
            } else {
                esp_zb_bdb_open_network(180);
                LOGI_TIME("Open nework for 180s ...");
            }
        }
        break;
    case ESP_ZB_BDB_SIGNAL_FORMATION:
        LOGI_TIME("Network formation status=%s", esp_err_to_name(err_status));
        if (err_status == ESP_OK) {
            LOGI_TIME("Pornesc network steering");
            esp_zb_bdb_start_top_level_commissioning(ESP_ZB_BDB_MODE_NETWORK_STEERING);
        }
        break;
    case ESP_ZB_BDB_SIGNAL_STEERING:
        LOGI_TIME("Network steering status=%s", esp_err_to_name(err_status));
        if (err_status == ESP_OK) {
            LOGI_TIME("Network steering successful, device joined network");
        } else {
            LOGE_TIME("Network steering failed, status=%s", esp_err_to_name(err_status));
        }
        break;
    case ESP_ZB_ZDO_SIGNAL_DEVICE_ANNCE: {
        dev_annce_params =
            (esp_zb_zdo_signal_device_annce_params_t *)
            esp_zb_app_signal_get_params(p_sg_p);
        uint16_t short_addr = dev_annce_params->device_short_addr;
        w100_short_addr = short_addr;
        memcpy(aqara_ieee_addr, dev_annce_params->ieee_addr,
               sizeof(aqara_ieee_addr));
        
        LOGI_TIME("[W100] IEEE bytes=%02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x",
            (unsigned)aqara_ieee_addr[0], (unsigned)aqara_ieee_addr[1],
            (unsigned)aqara_ieee_addr[2], (unsigned)aqara_ieee_addr[3],
            (unsigned)aqara_ieee_addr[4], (unsigned)aqara_ieee_addr[5],
            (unsigned)aqara_ieee_addr[6], (unsigned)aqara_ieee_addr[7]);

        LOGI_TIME("DEVICE ANNCE primit de la 0x%04hx", short_addr);

        if (track_device(short_addr)) {
            if (xTaskCreate(task_configurare_aqara, "task_config_aqara",
                            4096, (void *)(uintptr_t)short_addr, 5, NULL) != pdPASS) {
                untrack_device(short_addr);
                LOGE_TIME("Could not create configuration task");
            }
        }
        break;
    }
    case ESP_ZB_NWK_SIGNAL_PERMIT_JOIN_STATUS: {
        uint8_t *duration =
            (uint8_t *)esp_zb_app_signal_get_params(p_sg_p);

        if (err_status == ESP_OK && duration != NULL) {
            if (*duration == 0) {
                LOGI_TIME("Fereastra de join s-a inchis.");
            } else {
                LOGI_TIME("Fereastra de join activa: %u secunde ramase.",
                          (unsigned)*duration);
            }
        } else {
            LOGW_TIME("Semnal permit-join cu status %s",
                      esp_err_to_name(err_status));
        }
        break;
    }
    case ESP_ZB_ZDO_SIGNAL_DEVICE_UPDATE: {
        esp_zb_zdo_signal_device_update_params_t *update =
            (esp_zb_zdo_signal_device_update_params_t *)
            esp_zb_app_signal_get_params(p_sg_p);

        if (update != NULL) {
            const char *status_name = "unknown";
            const char *action_name = "unknown";

            switch (update->status) {
            case ESP_ZB_ZDO_STANDARD_DEV_SECURED_REJOIN:
                status_name = "secured rejoin";
                break;
            case ESP_ZB_ZDO_STANDARD_DEV_UNSECURED_JOIN:
                status_name = "unsecured join";
                break;
            case ESP_ZB_ZDO_STANDARD_DEV_LEFT:
                status_name = "device left";
                break;
            case ESP_ZB_ZDO_STANDARD_DEV_TC_REJOIN:
                status_name = "Trust Center rejoin";
                break;
            }

            switch (update->tc_action) {
            case ESP_ZB_ZDO_TC_ACTION_AUTHORIZE:
                action_name = "authorize";
                break;
            case ESP_ZB_ZDO_TC_ACTION_DENY:
                action_name = "deny";
                break;
            case ESP_ZB_ZDO_TC_ACTION_IGNORE:
                action_name = "ignore";
                break;
            }

            LOGI_TIME("[DEVICE UPDATE] addr=0x%04hx status=%s (0x%02x) "
                      "action=%s (0x%02x) parent=0x%04hx signal=%s",
                      update->short_addr,
                      status_name, (unsigned)update->status,
                      action_name, (unsigned)update->tc_action,
                      update->parent_short,
                      esp_err_to_name(err_status));
        }
        break;
    }
    default:
        LOGI_TIME("[ZB SIGNAL] neprocesat: type=%lu status=%s",
                  (unsigned long)sig_type, esp_err_to_name(err_status));
        break;
    }
}

static bool w100_parse_pmtsd(const char *text, size_t len,
                             w100_pmtsd_state_t *state)
{
    if (text == NULL || state == NULL || len == 0 || len > 42) {
        return false;
    }

    char input[43];
    memcpy(input, text, len);
    input[len] = '\0';

    unsigned p, m, s, d;
    float t;
    int consumed = 0;

    if (sscanf(input, "P%u_M%u_T%f_S%u_D%u%n",
               &p, &m, &t, &s, &d, &consumed) != 5 ||
        consumed != (int)len ||
        p > 1 || m > 3 || s > 9 || d > 9 ||
        t < 5.0f || t > 30.0f) {
        return false;
    }

    state->p = (uint8_t)p;
    state->m = (uint8_t)m;
    state->t = t;
    state->s = (uint8_t)s;
    state->d = (uint8_t)d;
    return true;
}

static bool w100_extract_pmtsd(const uint8_t *bytes, size_t size,
                               w100_pmtsd_state_t *state)
{
    if (bytes == NULL || state == NULL) {
        return false;
    }

    for (size_t i = 0; i + 3 <= size; i++) {
        if (bytes[i] != 0x08 || bytes[i + 1] != 0x44) {
            continue;
        }

        size_t text_len = bytes[i + 2];
        size_t text_pos = i + 3;

        if (text_len == 0 || text_len > 42 ||
            text_pos + text_len > size) {
            continue;
        }

        char text[43];
        memcpy(text, &bytes[text_pos], text_len);
        text[text_len] = '\0';

        w100_pmtsd_state_t parsed;
        portENTER_CRITICAL(&w100_pmtsd_mux);
        parsed = w100_pmtsd_state;
        portEXIT_CRITICAL(&w100_pmtsd_mux);

        bool found_field = false;
        char *token = text;

        while (token != NULL && *token != '\0') {
            char *next = strchr(token, '_');
            if (next != NULL) {
                *next = '\0';
                next++;
                if (*next == '\0') {
                    return false;
                }
            }

            if (token[0] == '\0' || token[1] == '\0') {
                return false;
            }

            const char *value = token + 1;
            int consumed = 0;
            unsigned number;
            float temperature;

            switch (token[0]) {
            case 'P':
                if (sscanf(value, "%u%n", &number, &consumed) != 1 ||
                    consumed != (int)strlen(value) || number > 1) {
                    return false;
                }
                parsed.p = (uint8_t)number;
                break;

            case 'M':
                if (sscanf(value, "%u%n", &number, &consumed) != 1 ||
                    consumed != (int)strlen(value) || number > 3) {
                    return false;
                }
                parsed.m = (uint8_t)number;
                break;

            case 'T':
                if (sscanf(value, "%f%n", &temperature, &consumed) != 1 ||
                    consumed != (int)strlen(value) ||
                    !(temperature >= 5.0f && temperature <= 30.0f)) {
                    return false;
                }
                parsed.t = temperature;
                break;

            case 'S':
                if (sscanf(value, "%u%n", &number, &consumed) != 1 ||
                    consumed != (int)strlen(value) || number > 9) {
                    return false;
                }
                parsed.s = (uint8_t)number;
                break;

            case 'D':
                if (sscanf(value, "%u%n", &number, &consumed) != 1 ||
                    consumed != (int)strlen(value) || number > 9) {
                    return false;
                }
                parsed.d = (uint8_t)number;
                break;

            default:
                return false;
            }

            found_field = true;
            token = next;
        }

        if (found_field) {
            *state = parsed;
            return true;
        }
    }

    return false;
}

static bool w100_store_pmtsd(const w100_pmtsd_state_t *state)
{
    bool setpoint_changed;

    portENTER_CRITICAL(&w100_pmtsd_mux);
    setpoint_changed = setpoint_temperatura != state->t;
    w100_pmtsd_state = *state;
    setpoint_temperatura = state->t;
    portEXIT_CRITICAL(&w100_pmtsd_mux);

    return setpoint_changed;
}

static void task_w100_read_control_attr(void *arg)
{
    uint16_t short_addr = (uint16_t)(uintptr_t)arg;
    static uint16_t attr_ids[] = {0x0012, 0x0014, 0x0401};

    esp_zb_zcl_read_attr_cmd_t cmd = {0};
    cmd.zcl_basic_cmd.dst_addr_u.addr_short = short_addr;
    cmd.zcl_basic_cmd.dst_endpoint = 1;
    cmd.zcl_basic_cmd.src_endpoint = ESP_ZB_GATEWAY_ENDPOINT;
    cmd.address_mode = ESP_ZB_APS_ADDR_MODE_16_ENDP_PRESENT;
    cmd.clusterID = 0xFCC0;
    cmd.attr_number = sizeof(attr_ids) / sizeof(attr_ids[0]);
    cmd.attr_field = attr_ids;
    cmd.manuf_specific = 1;
    cmd.manuf_code = 0x115F;

    esp_zb_lock_acquire(portMAX_DELAY);
    uint8_t tsn = esp_zb_zcl_read_attr_cmd_req(&cmd);
    esp_zb_lock_release();

    LOGI_TIME("[W100 ATTR READ TX] cluster=0xFCC0 attrs=0012,0014,0401 "
              "manuf=0x115F addr=0x%04hx EP=1 TSN=%u",
              short_addr, (unsigned)tsn);
    vTaskDelete(NULL);
}

static esp_err_t zb_action_handler(esp_zb_core_action_callback_id_t callback_id,
                                   const void *message)
{
    esp_err_t ret = ESP_OK;

    switch (callback_id) {
    case ESP_ZB_CORE_REPORT_ATTR_CB_ID: {
        const esp_zb_zcl_report_attr_message_t *report = message;

        if (report != NULL) {
            LOGI_TIME("[ATTR REPORT RX] cluster=0x%04hx attr=0x%04hx "
                      "src_ep=%u status=0x%02x type=0x%02x size=%u",
                      report->cluster, report->attribute.id,
                      report->src_endpoint, (unsigned)report->status,
                      (unsigned)report->attribute.data.type,
                      (unsigned)report->attribute.data.size);
        }

        if (report == NULL || report->status != ESP_ZB_ZCL_STATUS_SUCCESS ||
            report->attribute.data.value == NULL) {
            LOGW_TIME("[REPORT] mesaj invalid sau status=0x%02x",
                      report ? (unsigned)report->status : 0xff);
            break;
        }

        if (report->cluster != 0xFCC0) {
            const uint8_t *value = report->attribute.data.value;
            size_t size = report->attribute.data.size;
            size_t count = size < 64 ? size : 64;
            char hex[2 * 64 + 1];

            for (size_t i = 0; i < count; i++) {
                snprintf(&hex[2 * i], sizeof(hex) - 2 * i,
                         "%02x", value[i]);
            }
            hex[2 * count] = '\0';

            LOGI_TIME("[REPORT RAW] cluster=0x%04hx EP=%u attr=0x%04hx "
                      "type=0x%02x size=%u data=%s%s",
                      report->cluster, report->src_endpoint,
                      report->attribute.id,
                      (unsigned)report->attribute.data.type,
                      (unsigned)size, hex,
                      size > count ? " (truncated)" : "");
        }

        if (report->cluster == 0xFCC0) {
            const uint8_t *bytes = report->attribute.data.value;
            size_t size = report->attribute.data.size;
            char hex[129];
            size_t count = size < 64 ? size : 64;

            for (size_t i = 0; i < count; i++) {
                snprintf(&hex[2 * i], sizeof(hex) - 2 * i,
                         "%02x", bytes[i]);
            }
            hex[2 * count] = '\0';

            LOGI_TIME("[W100 RX] attr=0x%04hx type=0x%02x size=%u data=%s",
                      report->attribute.id,
                      (unsigned)report->attribute.data.type,
                      (unsigned)size, hex);
                      char ascii[65];
            for (size_t i = 0; i < count; i++) {
                ascii[i] = (bytes[i] >= 0x20 && bytes[i] <= 0x7e)
                               ? (char)bytes[i]
                               : '.';
            }
            ascii[count] = '\0';
            LOGI_TIME("[W100 RX ASCII] attr=0x%04hx: %s",
                      report->attribute.id, ascii);
            // Raport generic observat la apăsarea butoanelor.
            // Ignorăm contorul/checksum-ul variabil și potrivim restul cadrului.
            static const uint8_t sync_prefix[] = {0xAA, 0x71, 0x0F, 0x84};
            static const uint8_t sync_suffix[] = {
                0x06, 0x41, 0x0F, 0x00, 0x00, 0x54, 0xEF, 0x44,
                0x80, 0x71, 0x1A, 0x08, 0x00, 0x08, 0x44
            };

            if (report->attribute.id == 0xFFF2 && size == 22 &&
                bytes[0] == 0x15 &&
                memcmp(&bytes[1], sync_prefix, sizeof(sync_prefix)) == 0 &&
                memcmp(&bytes[7], sync_suffix, sizeof(sync_suffix)) == 0) {
                LOGI_TIME("[W100 SYNC] eveniment buton; trimit starea PMTSD memorată");

                w100_sync_args_t *args = pvPortMalloc(sizeof(*args));
                if (args != NULL) {
                    args->short_addr = w100_short_addr;
                    args->endpoint = report->src_endpoint;

                    if (xTaskCreate(task_w100_sync_reply, "w100_sync_reply",
                                    3072, args, 4, NULL) != pdPASS) {
                        vPortFree(args);
                        LOGE_TIME("[W100 SYNC] Nu s-a putut porni task-ul");
                    }
                } else {
                    LOGE_TIME("[W100 SYNC] Memorie insuficienta");
                }
            }

            if (report->attribute.id == 0xFFF2) {
                w100_pmtsd_state_t received;

                if (w100_extract_pmtsd(bytes, size, &received)) {
                    bool setpoint_changed = w100_store_pmtsd(&received);

                    LOGI_TIME("[W100 PMTSD] primit P%u_M%u_T%.1f_S%u_D%u",
                              received.p, received.m, (double)received.t,
                              received.s, received.d);

                    if (setpoint_changed && temperatura_curenta > 0.0f) {
                        ruleaza_logica_termostat();
                    }
                }
            }
        }

        if (report->cluster == ESP_ZB_ZCL_CLUSTER_ID_TEMP_MEASUREMENT &&
            report->attribute.id == 0x0000) {
            int16_t raw = 0;
            memcpy(&raw, report->attribute.data.value, sizeof(raw));
            float temp = (float)raw / 100.0f;

            LOGI_TIME("[REPORT] temperatura EP %u: %.1f C (raw=%u)",
                      report->src_endpoint, temp, raw);

            temperatura_curenta = temp;
            ruleaza_logica_termostat();
        } else if (report->cluster ==
                    ESP_ZB_ZCL_CLUSTER_ID_REL_HUMIDITY_MEASUREMENT &&
                report->attribute.id == 0x0000) {
            uint16_t raw = 0;
            memcpy(&raw, report->attribute.data.value, sizeof(raw));
            umiditate_curenta = (raw + 50U) / 100U;

            LOGI_TIME("[REPORT] umiditate EP %u: %u %% (raw=%u)",
                      report->src_endpoint, umiditate_curenta, raw);
            ruleaza_logica_umiditate();
        } else {
            LOGI_TIME("[REPORT] cluster=0x%04hx attr=0x%04hx EP %u",
                    report->cluster, report->attribute.id,
                    report->src_endpoint);
        }
        break;
    }
    case ESP_ZB_CORE_CMD_READ_ATTR_RESP_CB_ID: {
        esp_zb_zcl_cmd_read_attr_resp_message_t *read_resp = (esp_zb_zcl_cmd_read_attr_resp_message_t *)message;
        
        if (read_resp != NULL && read_resp->info.cluster == 0x0201) {
            for (esp_zb_zcl_read_attr_resp_variable_t *var =
                     read_resp->variables;
                 var != NULL; var = var->next) {
                if (var->attribute.id != 0x0012) {
                    continue;
                }

                if (var->attribute.data.value != NULL &&
                    var->attribute.data.size == sizeof(int16_t)) {
                    int16_t raw = 0;
                    memcpy(&raw, var->attribute.data.value, sizeof(raw));
                    LOGI_TIME("[W100 NATIVE READ RX] attr=0x0012 "
                              "type=0x%02x raw=%d setpoint=%.2f C",
                              (unsigned)var->attribute.data.type,
                              (int)raw, (double)raw / 100.0);
                } else {
                    LOGW_TIME("[W100 NATIVE READ RX] attr=0x0012 "
                              "type=0x%02x size=%u value=%s",
                              (unsigned)var->attribute.data.type,
                              (unsigned)var->attribute.data.size,
                              var->attribute.data.value ? "present" : "NULL");
                }
            }
        }

        if (read_resp != NULL && read_resp->info.cluster == 0xFCC0) {
            for (const esp_zb_zcl_read_attr_resp_variable_t *var =
                     read_resp->variables;
                 var != NULL; var = var->next) {
                uint16_t id = var->attribute.id;
                if (id != 0x0012 && id != 0x0014 && id != 0x0401) {
                    continue;
                }

                const uint8_t *value = var->attribute.data.value;
                size_t size = value ? var->attribute.data.size : 0;
                char hex[129];
                size_t count = size < 64 ? size : 64;

                for (size_t i = 0; i < count; i++) {
                    snprintf(&hex[2 * i], sizeof(hex) - 2 * i,
                             "%02x", value[i]);
                }
                hex[2 * count] = '\0';

                LOGI_TIME("[W100 ATTR READ RX] attr=0x%04hx type=0x%02x "
                          "size=%u raw=%s",
                          id, (unsigned)var->attribute.data.type,
                          (unsigned)size, value ? hex : "NULL");

                if (value && var->attribute.data.type == 0x21 && size == 2) {
                    uint16_t raw;
                    memcpy(&raw, value, sizeof(raw));
                    LOGI_TIME("[W100 ATTR READ RX] attr=0x%04hx uint16=%u",
                              id, (unsigned)raw);
                } else if (value &&
                           var->attribute.data.type == 0x23 && size == 4) {
                    uint32_t raw;
                    memcpy(&raw, value, sizeof(raw));
                    LOGI_TIME("[W100 ATTR READ RX] attr=0x%04hx uint32=%lu",
                              id, (unsigned long)raw);
                }
            }
        }

        if (read_resp == NULL) {
            LOGW_TIME("[W100 READ RX] mesaj NULL");
            break;
        }

        if (read_resp->info.cluster == ESP_ZB_ZCL_CLUSTER_ID_TEMP_MEASUREMENT || read_resp->info.cluster == 0x0402) {
            esp_zb_zcl_read_attr_resp_variable_t *variable = read_resp->variables;
            
            if (variable && variable->attribute.id == 0x0000 && variable->attribute.data.value) { 
                int16_t raw_temp = 0;
                memcpy(&raw_temp, variable->attribute.data.value, sizeof(int16_t));
                raw_temp /= 10;
                float temp = (float)raw_temp / 10.0;
                
                // RULĂM EVALUAREA: Printează decizia locală în funcție de temperatură
                if (temp != temperatura_curenta) {
                    temperatura_curenta = temp;
                    ruleaza_logica_termostat();
                }
            }
        } else if (read_resp->info.cluster == ESP_ZB_ZCL_CLUSTER_ID_REL_HUMIDITY_MEASUREMENT || read_resp->info.cluster == 0x0405) {
            esp_zb_zcl_read_attr_resp_variable_t *variable = read_resp->variables;
            if (variable && variable->attribute.id == 0x0000 && variable->attribute.data.value) {
                uint16_t raw_hum = 0; // Umiditatea vine ca Unsigned 16-bit
                memcpy(&raw_hum, variable->attribute.data.value, sizeof(uint16_t));
                raw_hum /= 100;
                if (raw_hum != umiditate_curenta) {
                    umiditate_curenta = raw_hum;
                    ruleaza_logica_umiditate();
                }
            }
        }
        return ESP_OK; 
    }
    case ESP_ZB_CORE_CMD_REPORT_CONFIG_RESP_CB_ID: {
        const esp_zb_zcl_cmd_config_report_resp_message_t *resp = message;

        if (resp == NULL) {
            LOGW_TIME("[REPORT CFG RESP] mesaj NULL");
            break;
        }

        const esp_zb_zcl_config_report_resp_variable_t *var = resp->variables;
        if (var == NULL) {
            LOGI_TIME("[REPORT CFG RESP] cluster=0x%04hx fără înregistrări",
                      resp->info.cluster);
        }

        for (; var != NULL; var = var->next) {
            LOGI_TIME("[REPORT CFG RESP] cluster=0x%04hx direction=%u "
                      "attr=0x%04hx status=0x%02x",
                      resp->info.cluster,
                      (unsigned)var->direction,
                      var->attribute_id,
                      (unsigned)var->status);
        }
        break;
    }
    case ESP_ZB_CORE_CMD_WRITE_ATTR_RESP_CB_ID: {
        const esp_zb_zcl_cmd_write_attr_resp_message_t *resp = message;

        if (resp == NULL) {
            LOGW_TIME("[W100 WRITE RESP] mesaj NULL");
            break;
        }

        LOGI_TIME("[W100 WRITE RESP] cluster=0x%04hx src_ep=%u "
                  "status=0x%02x",
                  resp->info.cluster,
                  resp->info.src_endpoint,
                  (unsigned)resp->info.status);

        for (const esp_zb_zcl_write_attr_resp_variable_t *var = resp->variables;
             var != NULL; var = var->next) {
            LOGI_TIME("[W100 WRITE RESP] attr=0x%04hx status=0x%02x",
                      var->attribute_id, (unsigned)var->status);
        }
        break;
    }
    case ESP_ZB_CORE_CMD_DISC_ATTR_RESP_CB_ID: {
        const esp_zb_zcl_cmd_discover_attributes_resp_message_t *resp = message;

        if (resp == NULL) {
            LOGW_TIME("[FCC0 DISC RESP] mesaj NULL");
            break;
        }

        LOGI_TIME("[FCC0 DISC RESP] cluster=0x%04hx src_ep=%u status=0x%02x "
                  "completed=%u",
                  resp->info.cluster, resp->info.src_endpoint,
                  (unsigned)resp->info.status, (unsigned)resp->is_completed);

        for (const esp_zb_zcl_disc_attr_variable_t *var = resp->variables;
             var != NULL; var = var->next) {
            LOGI_TIME("[FCC0 DISC RESP] attr=0x%04hx type=0x%02x",
                      var->attr_id, (unsigned)var->data_type);
        }
        break;
    }
    case ESP_ZB_CORE_CMD_CUSTOM_CLUSTER_REQ_CB_ID:
    case ESP_ZB_CORE_CMD_CUSTOM_CLUSTER_RESP_CB_ID: {
        const esp_zb_zcl_custom_cluster_command_message_t *custom = message;

        if (custom == NULL) {
            LOGW_TIME("[CUSTOM ZCL] callback=%d mesaj NULL", (int)callback_id);
            break;
        }

        LOGI_TIME("[CUSTOM ZCL] callback=%d cluster=0x%04hx src_ep=%u "
                  "dst_ep=%u status=0x%02x size=%u",
                  (int)callback_id,
                  custom->info.cluster,
                  custom->info.src_endpoint,
                  custom->info.dst_endpoint,
                  (unsigned)custom->info.status,
                  (unsigned)custom->data.size);

        const uint8_t *bytes = (const uint8_t *)custom->data.value;
        uint16_t count = custom->data.size < 32 ? custom->data.size : 32;

        if (bytes != NULL) {
            for (uint16_t i = 0; i < count; i++) {
                LOGI_TIME("[CUSTOM ZCL] data[%u]=0x%02x",
                          (unsigned)i, bytes[i]);
            }
        }
        break;
    }
    default:
        LOGI_TIME("[ZB ACTION] callback_id=%d unknown", (int)callback_id);
        break;
    }

    return ret;
}

static bool raw_zcl_command_handler(uint8_t bufid)
{
    zb_uint16_t len = zb_buf_len(bufid);
    zb_uint8_t *data = zb_buf_begin(bufid);
    size_t count = len < 64U ? len : 64U;
    char hex[2 * 64 + 1];

    if (data == NULL) {
        LOGW_TIME("[RAW ZCL] bufid=%u len=%u data=NULL",
                  (unsigned)bufid, (unsigned)len);
        return false;
    }

    for (size_t i = 0; i < count; i++) {
        snprintf(&hex[2 * i], sizeof(hex) - 2 * i, "%02x", data[i]);
    }
    hex[2 * count] = '\0';

    LOGI_TIME("[RAW ZCL] bufid=%u len=%u data=%s",
              (unsigned)bufid, (unsigned)len, hex);

    return false; // Doar inspectăm; stiva continuă procesarea normală.
}

static void esp_zb_task(void *pvParameters)
{
    esp_zb_cfg_t zb_nwk_cfg = ESP_ZB_ZC_CONFIG();
    esp_zb_init(&zb_nwk_cfg);
    esp_zb_set_primary_network_channel_set(ESP_ZB_PRIMARY_CHANNEL_MASK);
    esp_zb_ep_list_t *ep_list = esp_zb_ep_list_create();
    esp_zb_cluster_list_t *cluster_list = esp_zb_zcl_cluster_list_create();
    esp_zb_endpoint_config_t endpoint_config = {
        .endpoint = ESP_ZB_GATEWAY_ENDPOINT,
        .app_profile_id = ESP_ZB_AF_HA_PROFILE_ID,
        .app_device_id = ESP_ZB_HA_TEMPERATURE_SENSOR_DEVICE_ID,
        .app_device_version = 0,
    };

    esp_zb_attribute_list_t *basic_cluser = esp_zb_basic_cluster_create(NULL);
    esp_zb_cluster_list_add_basic_cluster(cluster_list, basic_cluser, ESP_ZB_ZCL_CLUSTER_SERVER_ROLE);
    esp_zb_cluster_list_add_temperature_meas_cluster(cluster_list, esp_zb_temperature_meas_cluster_create(NULL), ESP_ZB_ZCL_CLUSTER_CLIENT_ROLE);
    esp_zb_cluster_list_add_humidity_meas_cluster(cluster_list, esp_zb_humidity_meas_cluster_create(NULL), ESP_ZB_ZCL_CLUSTER_CLIENT_ROLE);

    esp_zb_ep_list_add_gateway_ep(ep_list, cluster_list, endpoint_config);
    esp_zb_core_action_handler_register(zb_action_handler);
    esp_zb_raw_command_handler_register(raw_zcl_command_handler);
    esp_zb_device_register(ep_list);
    ESP_ERROR_CHECK(esp_zb_start(false));
    esp_zb_stack_main_loop();
    vTaskDelete(NULL);
}

static void task_runtime_stats(void *arg)
{
    while (true) {
        size_t free_heap = heap_caps_get_free_size(MALLOC_CAP_8BIT);
        size_t min_heap = heap_caps_get_minimum_free_size(MALLOC_CAP_8BIT);
        size_t largest_block = heap_caps_get_largest_free_block(MALLOC_CAP_8BIT);
        UBaseType_t task_count = uxTaskGetNumberOfTasks();
        UBaseType_t stack_margin = uxTaskGetStackHighWaterMark(NULL);

        LOGI_TIME("[STATS] heap free=%u min=%u largest_block=%u bytes; "
                  "tasks=%u; stats_task_stack_margin=%u",
                  (unsigned)free_heap,
                  (unsigned)min_heap,
                  (unsigned)largest_block,
                  (unsigned)task_count,
                  (unsigned)stack_margin);

        vTaskDelay(pdMS_TO_TICKS(60000));
    }
}

static void pmtsd_send_console_line(uint16_t short_addr, uint8_t endpoint,
                                    const char *line, size_t len)
{
    if (len == 0 || len > 42) {
        return;
    }

    if (short_addr == 0) {
        printf("W100 nu este inca disponibil.\n");
        fflush(stdout);
        return;
    }

    for (size_t i = 0; i < len; i++) {
        unsigned char c = (unsigned char)line[i];
        if (c < 0x20 || c > 0x7e) {
            printf("Foloseste doar caractere ASCII imprimabile.\n");
            fflush(stdout);
            return;
        }
    }

    w100_pmtsd_state_t entered_state;
    if (w100_parse_pmtsd(line, len, &entered_state)) {
        bool setpoint_changed = w100_store_pmtsd(&entered_state);
        LOGI_TIME("[PMTSD] stare memorată P%u_M%u_T%.1f_S%u_D%u",
                  entered_state.p, entered_state.m,
                  (double)entered_state.t, entered_state.s, entered_state.d);

        if (setpoint_changed && temperatura_curenta > 0.0f) {
            ruleaza_logica_termostat();
        }
    } else {
        LOGW_TIME("[PMTSD] comanda nu este PMTSD complet valid; "
                  "o trimit pentru test, fără să schimb starea memorată");
    }

    uint8_t frame[64] = {
        0xaa, 0x71, 0x00, 0x44, 0x00, 0x00, 0x05, 0x41, 0x1c,
        0x00, 0x00, 0x54, 0xef, 0x44, 0x80, 0x71, 0x1a, 0x08,
        0x00, 0x08, 0x44, (uint8_t)len
    };

    frame[2] = (uint8_t)(14U + len);
    frame[4] = w100_pmtsd_counter++;
    memcpy(&frame[22], line, len);

    uint8_t checksum = 0;
    for (size_t i = 0; i < 22U + len; i++) {
        checksum = (uint8_t)(checksum + frame[i]);
    }
    frame[5] = checksum;

    w100_log_frame("PMTSD CONSOLE", frame, 22U + len);
    uint8_t tsn = w100_write_octet_frame(short_addr, endpoint,
                                     frame, 22U + len);

    LOGI_TIME("[PMTSD CONSOLE] text=\"%.*s\" TSN=%u",
              (int)len, line, (unsigned)tsn);
    printf("Comanda trimisa: %.*s\n", (int)len, line);
    fflush(stdout);
}

static void task_pmtsd_console(void *arg)
{
    char chunk[128];
    char pending[43]; // maximum 42 caractere PMTSD
    size_t pending_len = 0;
    bool dropping_line = false;

    printf("\nPMTSD: tasteaza textul complet si apasa Enter.\n");
    printf("Exemple: P0_M1_T24 | P0_S0 | M0_T24 | P1\n");
    fflush(stdout);

    while (true) {
        if (fgets(chunk, sizeof(chunk), stdin) == NULL) {
            clearerr(stdin);
            vTaskDelay(pdMS_TO_TICKS(50));
            continue;
        }

        // fgets poate returna fragmente; nu trimitem nimic până la Enter.
        for (size_t i = 0; chunk[i] != '\0'; i++) {
            char c = chunk[i];

            if (c == '\r' || c == '\n') {
                if (dropping_line) {
                    printf("Text prea lung; comanda nu a fost trimisa.\n");
                    fflush(stdout);
                } else if (pending_len > 0) {
                    pmtsd_send_console_line(w100_short_addr, 1, pending, pending_len);
                }

                pending_len = 0;
                dropping_line = false;
                continue;
            }

            if (dropping_line) {
                continue;
            }

            if (pending_len < 42) {
                pending[pending_len++] = c;
            } else {
                dropping_line = true;
                pending_len = 0;
            }
        }
    }
}

void app_main(void)
{
    ESP_ERROR_CHECK(nvs_flash_init());

    // Connect to the Wi-Fi network configured in menuconfig.
    ESP_ERROR_CHECK(esp_netif_init());
    ESP_ERROR_CHECK(esp_event_loop_create_default());

    esp_zb_platform_config_t config = {
        .radio_config = ESP_ZB_DEFAULT_RADIO_CONFIG(),
        .host_config = ESP_ZB_DEFAULT_HOST_CONFIG(),
    };
    ESP_ERROR_CHECK(esp_zb_platform_config(&config));
    xTaskCreate(esp_zb_task, "Zigbee_main", 8192, NULL, 5, NULL);

    if (xTaskCreate(task_pmtsd_console, "pmtsd_console", 4096,
                    NULL, 2, NULL) != pdPASS) {
        ESP_LOGE(TAG, "Nu s-a putut porni consola PMTSD");
    }

    // Create a task to monitor heap usage
    if (xTaskCreate(task_runtime_stats, "runtime_stats", 3072,
                    NULL, 1, NULL) != pdPASS) {
        ESP_LOGE(TAG, "Could not create runtime stats task");
    }
}


