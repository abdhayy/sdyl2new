#!/usr/bin/python3
import RPi.GPIO as GPIO
import time
from datetime import datetime, timedelta
import json
import os
import uuid
import paho.mqtt.client as mqtt
import requests

from sdy_persistence import ProductionOutboxSender, ProductionSQLiteStore
from sdy_shift_schedule import (
    calculate_shift_end_datetime,
    coerce_bool,
    hour_slot_for_shift_end,
)

# ==========================================
# PIN CONFIGURATION & SETUP
# ==========================================
# [SDY2 THREE INPUTS] Match SDY1 reference BCM pins; verify actual wiring before use.
WATERJET_1_PIN = 5
WATERJET_2_PIN = 27
MF_LIMIT_SWITCH_PIN = 26
GPIO.setmode(GPIO.BCM)
for pin in (WATERJET_1_PIN, WATERJET_2_PIN, MF_LIMIT_SWITCH_PIN):
    GPIO.setup(pin, GPIO.IN, pull_up_down=GPIO.PUD_UP)

# Input polarity assumes voltage-safe active-LOW signals. Confirm against wiring.
SENSOR_ACTIVE_LEVEL = GPIO.LOW
SENSOR_DEBOUNCE_TIME = 0.05
MF_MIN_EVENT_INTERVAL_SECONDS = 2.0  # Reference SDY1 limit-switch lockout


# ==========================================
# GLOBAL VARIABLES & COUNTERS
# ==========================================
# Shift Totals
run_time = loading_time = delay_time = downtime = 0.0
total_rest_time = planned_stop_time = model_change_time = total_machine_time = 0.0

# Real Operating Time (resets on shift end and model change)
real_operating_time = 0.0
# Total Real Operating Time (resets on shift end ONLY)
total_real_operating_time = 0.0
# Tracks active time for the current batch (resets on model change & shift end)
batch_run_time = 0.0

# Output Trackers
total_output = 0            # Product count (resets on model change)
shift_total_output = 0      # Total product count (resets on shift end only)
hourly_output = 0
total_rejects = 0           # Sum of dashboard rejects received via MQTT
mf_count = 0                # Separate MF counter, model-scoped
waterjet_1_count = 0        # Diagnostic counters, model-scoped
waterjet_2_count = 0

# Hourly Trackers
hourly_rest_time = 0.0
lost_time_this_hour = 0.0
base_time_this_hour = 0.0   # Accurately tracks base time even if model changes mid-hour

# Sensor & Cycle Trackers
sensor_blocked = False
blockage_start_time = 0.0
current_cycle_time = 0.0

# Debounced, independently armed inputs. Initialized to current level to
# avoid a false count if the process starts while an object is detected.
class DebouncedInput:
    def __init__(self, pin, debounce_seconds=SENSOR_DEBOUNCE_TIME):
        self.pin = pin
        self.debounce_seconds = debounce_seconds
        self.stable = GPIO.input(pin)
        self.candidate = self.stable
        self.since = time.monotonic()

    def poll_press(self, now):
        level = GPIO.input(self.pin)
        if level != self.candidate:
            self.candidate = level
            self.since = now
        if level != self.stable and now - self.since >= self.debounce_seconds:
            self.stable = level
            return level == SENSOR_ACTIVE_LEVEL
        return False

waterjet_1_input = DebouncedInput(WATERJET_1_PIN)
waterjet_2_input = DebouncedInput(WATERJET_2_PIN)
mf_input = DebouncedInput(MF_LIMIT_SWITCH_PIN)
last_mf_event_time = float('-inf')

# ==========================================
# MQTT & GOOGLE SHEETS CONFIGURATION
# ==========================================
LINE_CODE = "SDY2"
PRODUCTION_DAY_BOUNDARY_HOUR = 8
SHIFT_ENTRY_GRACE_MINUTES = 45
MQTT_BROKER = "localhost"
MQTT_PORT = 1883
MQTT_TOPIC_DATA = "sensor2/data"
MQTT_TOPIC_STATUS = "sdy2/status"

# Node-RED Topics
MQTT_TOPIC_SHIFT_FORM = "nodered/newshift"
MQTT_TOPIC_SETUP = "nodered/modeltarget"
MQTT_TOPIC_NR_REJECT = "nodered/reject"
MQTT_TOPIC_NR_DOWNTIME = "nodered/downtime"
MQTT_TOPIC_NR_ENDSHIFT = "nodered/endshift"
MQTT_TOPIC_MODE = "nodered/mode"
MQTT_TOPIC_PARAM_CONDITION = "noderedparam/condition"
MQTT_TOPIC_ADJUST_COUNT = "nodered/adjust_count"

# Live PRS dashboard topics
MQTT_TOPIC_LIVE_HOURLY = "smartchecksheet/hourly"
MQTT_TOPIC_LIVE_SNAPSHOT = "smartchecksheet/live"

# Google Sheets Web App URL
WEB_APP_URL = "https://script.google.com/macros/s/AKfycbyVm-Ghh2w3sQfWnh1A7mQTXZb4F3XOdE681GiVIynpvrXPE3dJ_769NxmucZT6O1fxqQ/exec"

SCRIPT_DIRECTORY = os.path.dirname(os.path.abspath(__file__))
SQLITE_DATABASE_PATH = os.environ.get(
    "SDY2_SQLITE_PATH", os.path.join(SCRIPT_DIRECTORY, "runtime", "sdy2_state.db")
)
TRUSTED_API_ENABLED = os.environ.get("SDY2_API_ENABLED", "false").lower() in {
    "1", "true", "yes", "on"
}
TRUSTED_API_EVENTS_URL = os.environ.get("SDY2_API_EVENTS_URL", "")
TRUSTED_API_KEY = os.environ.get("SDY2_API_KEY", "")
STATE_CHECKPOINT_INTERVAL_SECONDS = 5.0

# ==========================================
# STATE & SHIFT MANAGEMENT
# ==========================================
STATUS_RUN = 0
STATUS_LOADING = 1
STATUS_DELAY = 2
STATUS_REST = 3
STATUS_DOWN = 4
STATUS_PLANNED_STOP = 5
STATUS_MODEL_CHANGE = 6
STATUS_WAITING_FOR_SHIFT = 7

MODE_NORMAL = "NORMAL"
MODE_DOWN = "DOWN"
MODE_MODEL_CHANGE = "MODEL CHANGE"
MODE_REST = "REST"
MODE_PLANNED_STOP = "PLANNED STOP"

current_mode = MODE_NORMAL
current_status = STATUS_RUN
previous_status = STATUS_RUN
last_sent_hour = -1
last_live_snapshot_publish = 0.0
last_runtime_checkpoint = 0.0
recovered_from_sqlite = False
shift_entry_window_started_at = None
shift_entry_window_ends_at = None

current_shift = {
    "shift_id": "NO PROD", "line": "NO PROD", "date": "NO PROD", "shift": "NO PROD", "group": "-",
    "model": "NO PROD", "lot_number": "NO PROD", "target": 0, "standard_cycle": 1.0,
    "supervisor": "-", "leader": "-", "workingTime": "-", "overtime": False,
    "scheduled_end_at": None,
    "forming": "-", "waterjet": "-", "assembly": "-", "quality": "-"
}

google_sheets_queue = []

persistence_store = None
outbox_sender = None
try:
    persistence_store = ProductionSQLiteStore(SQLITE_DATABASE_PATH)
    outbox_sender = ProductionOutboxSender(
        persistence_store,
        TRUSTED_API_EVENTS_URL,
        TRUSTED_API_KEY,
        TRUSTED_API_ENABLED,
        "sdy2-api-outbox",
    )
except Exception as exc:
    print(f"[SQLITE CRITICAL] Persistence disabled; production continues: {exc}")

def safe_int(val):
    try:
        return int(val)
    except (ValueError, TypeError):
        return 0

def get_hour_slot(dt=None):
    if dt is None:
        dt = datetime.now()
    start_hour = dt.hour
    end_hour = (start_hour + 1) % 24
    return f"{start_hour}.00-{end_hour}.00"


def get_current_shift_end_datetime():
    if current_shift.get("shift_id") == "NO PROD":
        return None
    stored_end = current_shift.get("scheduled_end_at")
    if stored_end:
        try:
            return datetime.fromisoformat(stored_end)
        except (TypeError, ValueError):
            print(f"[SCHEDULE WARNING] Invalid saved shift end: {stored_end!r}")
    try:
        shift_end = calculate_shift_end_datetime(
            current_shift.get("date"),
            current_shift.get("shift"),
            current_shift.get("overtime", False),
            current_shift.get("workingTime"),
        )
        current_shift["scheduled_end_at"] = shift_end.isoformat()
        return shift_end
    except ValueError as exc:
        print(f"[SCHEDULE ERROR] Cannot calculate shift end: {exc}")
        return None


def build_runtime_snapshot():
    return {
        "schema_version": 1,
        "current_shift": dict(current_shift),
        "current_mode": current_mode,
        "current_status": current_status,
        "last_sent_hour": last_sent_hour,
        "sensor_blocked": sensor_blocked,
        "shift_entry_window": {
            "started_at": shift_entry_window_started_at,
            "ends_at": shift_entry_window_ends_at,
        },
        "counters": {
            "total_output": total_output,
            "shift_total_output": shift_total_output,
            "hourly_output": hourly_output,
            "total_rejects": total_rejects,
            "mf_count": mf_count,
            "waterjet_1_count": waterjet_1_count,
            "waterjet_2_count": waterjet_2_count,
        },
        "cycle": {"current_cycle_time": current_cycle_time},
        "timers": {
            "run_time": run_time,
            "loading_time": loading_time,
            "delay_time": delay_time,
            "downtime": downtime,
            "total_rest_time": total_rest_time,
            "planned_stop_time": planned_stop_time,
            "model_change_time": model_change_time,
            "total_machine_time": total_machine_time,
            "real_operating_time": real_operating_time,
            "total_real_operating_time": total_real_operating_time,
            "batch_run_time": batch_run_time,
            "hourly_rest_time": hourly_rest_time,
            "lost_time_this_hour": lost_time_this_hour,
            "base_time_this_hour": base_time_this_hour,
        },
        "saved_at": datetime.now().astimezone().isoformat(),
    }


def runtime_state_status():
    if shift_entry_window_is_active():
        return "WAITING_FOR_SHIFT"
    return "ACTIVE" if current_shift.get("shift_id") != "NO PROD" else "NO_PROD"


def checkpoint_runtime_state(force=False, reason="periodic"):
    global last_runtime_checkpoint
    if persistence_store is None:
        return False
    now = time.time()
    if not force and now - last_runtime_checkpoint < STATE_CHECKPOINT_INTERVAL_SECONDS:
        return True
    try:
        persistence_store.save_runtime_state(
            LINE_CODE, build_runtime_snapshot(), runtime_state_status()
        )
        last_runtime_checkpoint = now
        return True
    except Exception as exc:
        print(f"[SQLITE ERROR] Runtime checkpoint failed ({reason}): {exc}")
        return False


def checkpoint_and_queue_event(event_type, payload, shift_id=None, event_id=None):
    global last_runtime_checkpoint
    if persistence_store is None:
        print(f"[SQLITE ERROR] Cannot queue {event_type}; persistence is unavailable.")
        return None
    try:
        stable_id = persistence_store.save_state_and_enqueue(
            line_code=LINE_CODE,
            state=build_runtime_snapshot(),
            state_status=runtime_state_status(),
            event_type=event_type,
            shift_id=shift_id or current_shift.get("shift_id", "NO PROD"),
            payload=payload,
            event_id=event_id,
            occurred_at=datetime.now().astimezone().isoformat(),
        )
        last_runtime_checkpoint = time.time()
        print(f"[SQLITE] Queued {event_type} ({stable_id}).")
        return stable_id
    except Exception as exc:
        print(f"[SQLITE ERROR] Failed to queue {event_type}: {exc}")
        return None


def restore_runtime_state():
    global run_time, loading_time, delay_time, downtime
    global total_rest_time, planned_stop_time, model_change_time, total_machine_time
    global real_operating_time, total_real_operating_time, batch_run_time
    global total_output, shift_total_output, hourly_output, total_rejects
    global mf_count, waterjet_1_count, waterjet_2_count
    global hourly_rest_time, lost_time_this_hour, base_time_this_hour
    global current_cycle_time, current_mode, current_status, last_sent_hour
    global current_shift, sensor_blocked, recovered_from_sqlite
    global shift_entry_window_started_at, shift_entry_window_ends_at

    if persistence_store is None:
        return False
    try:
        snapshot = persistence_store.load_runtime_state(LINE_CODE)
    except Exception as exc:
        print(f"[SQLITE ERROR] Could not restore state: {exc}")
        return False
    if snapshot is None:
        checkpoint_runtime_state(force=True, reason="first startup")
        return False

    restored_shift = snapshot.get("current_shift", {})
    if isinstance(restored_shift, dict):
        current_shift.update(restored_shift)
    counters = snapshot.get("counters", {})
    timers = snapshot.get("timers", {})
    entry_window = snapshot.get("shift_entry_window", {})
    total_output = int(counters.get("total_output", 0))
    shift_total_output = int(counters.get("shift_total_output", 0))
    hourly_output = int(counters.get("hourly_output", 0))
    total_rejects = int(counters.get("total_rejects", 0))
    mf_count = int(counters.get("mf_count", 0))
    waterjet_1_count = int(counters.get("waterjet_1_count", 0))
    waterjet_2_count = int(counters.get("waterjet_2_count", 0))
    current_cycle_time = float(snapshot.get("cycle", {}).get("current_cycle_time", 0.0))
    run_time = float(timers.get("run_time", 0.0))
    loading_time = float(timers.get("loading_time", 0.0))
    delay_time = float(timers.get("delay_time", 0.0))
    downtime = float(timers.get("downtime", 0.0))
    total_rest_time = float(timers.get("total_rest_time", 0.0))
    planned_stop_time = float(timers.get("planned_stop_time", 0.0))
    model_change_time = float(timers.get("model_change_time", 0.0))
    total_machine_time = float(timers.get("total_machine_time", 0.0))
    real_operating_time = float(timers.get("real_operating_time", 0.0))
    total_real_operating_time = float(timers.get("total_real_operating_time", 0.0))
    batch_run_time = float(timers.get("batch_run_time", 0.0))
    hourly_rest_time = float(timers.get("hourly_rest_time", 0.0))
    lost_time_this_hour = float(timers.get("lost_time_this_hour", 0.0))
    base_time_this_hour = float(timers.get("base_time_this_hour", 0.0))
    current_mode = str(snapshot.get("current_mode", MODE_NORMAL))
    current_status = int(snapshot.get("current_status", STATUS_RUN))
    last_sent_hour = int(snapshot.get("last_sent_hour", -1))
    shift_entry_window_started_at = entry_window.get("started_at")
    shift_entry_window_ends_at = entry_window.get("ends_at")
    sensor_blocked = False
    recovered_from_sqlite = True
    print(
        f"[SQLITE] Restored {LINE_CODE}: Shift={current_shift.get('shift_id')} | "
        f"Hourly={hourly_output} | Model={total_output} | Shift Total={shift_total_output}"
    )
    return True

def get_stable_machine_state():
    """Either waterjet detector active indicates loading (SDY2 90s threshold kept)."""
    return int(
        waterjet_1_input.stable == SENSOR_ACTIVE_LEVEL
        or waterjet_2_input.stable == SENSOR_ACTIVE_LEVEL
    )

def reset_production_runtime_counters():
    global run_time, loading_time, delay_time, downtime, total_rest_time, planned_stop_time, model_change_time
    global total_machine_time, total_output, hourly_output, hourly_rest_time, lost_time_this_hour, base_time_this_hour
    global sensor_blocked, shift_total_output, total_rejects, current_cycle_time, real_operating_time
    global total_real_operating_time, batch_run_time, last_sent_hour
    global mf_count, waterjet_1_count, waterjet_2_count

    run_time = loading_time = delay_time = downtime = 0.0
    total_rest_time = planned_stop_time = model_change_time = total_machine_time = 0.0
    total_output = hourly_output = shift_total_output = total_rejects = 0
    mf_count = waterjet_1_count = waterjet_2_count = 0
    hourly_rest_time = lost_time_this_hour = base_time_this_hour = 0.0
    real_operating_time = total_real_operating_time = current_cycle_time = batch_run_time = 0.0
    sensor_blocked = False
    last_sent_hour = -1


def parse_shift_entry_datetime(value):
    if not value:
        return None
    try:
        return datetime.fromisoformat(str(value))
    except (TypeError, ValueError):
        return None


def shift_entry_window_is_active(moment=None):
    moment = moment or datetime.now()
    window_end = parse_shift_entry_datetime(shift_entry_window_ends_at)
    return window_end is not None and moment < window_end


def clear_shift_entry_window():
    global shift_entry_window_started_at, shift_entry_window_ends_at
    shift_entry_window_started_at = None
    shift_entry_window_ends_at = None


def start_shift_entry_window(boundary_time):
    global shift_entry_window_started_at, shift_entry_window_ends_at
    window_end = boundary_time + timedelta(minutes=SHIFT_ENTRY_GRACE_MINUTES)
    if datetime.now() >= window_end:
        clear_shift_entry_window()
        return False
    shift_entry_window_started_at = boundary_time.isoformat()
    shift_entry_window_ends_at = window_end.isoformat()
    checkpoint_runtime_state(force=True, reason="shift entry window started")
    print(
        "[SHIFT BUFFER] Waiting for the next shift form until "
        f"{window_end.strftime('%Y-%m-%d %I:%M %p')}."
    )
    return True


def expire_shift_entry_window(moment=None):
    moment = moment or datetime.now()
    window_end = parse_shift_entry_datetime(shift_entry_window_ends_at)
    if window_end is None or moment < window_end:
        return False
    print(
        f"[SHIFT BUFFER] No form received in {SHIFT_ENTRY_GRACE_MINUTES} minutes; "
        f"discarding {shift_total_output} unassigned product(s)."
    )
    reset_production_runtime_counters()
    clear_shift_entry_window()
    checkpoint_runtime_state(force=True, reason="shift entry window expired")
    return True


def reset_shift_data(save_checkpoint=True):
    global current_shift

    print("\n[EVENT] Executing Shift Data Reset...")
    reset_production_runtime_counters()
    clear_shift_entry_window()

    current_shift = {
        "shift_id": "NO PROD", "line": "NO PROD", "date": "NO PROD", "shift": "NO PROD", "group": "-",
        "model": "NO PROD", "lot_number": "NO PROD", "target": 0, "standard_cycle": 1.0,
        "supervisor": "-", "leader": "-", "workingTime": "-", "overtime": False,
        "scheduled_end_at": None,
        "forming": "-", "waterjet": "-", "assembly": "-", "quality": "-"
    }

    if save_checkpoint:
        checkpoint_runtime_state(force=True, reason="shift reset")


def production_day_key(moment):
    return (moment - timedelta(hours=PRODUCTION_DAY_BOUNDARY_HOUR)).date()


def current_shift_matches_production_day(moment):
    if current_shift.get("shift_id") == "NO PROD":
        return False
    shift_date = None
    for date_format in ("%Y-%m-%d", "%Y%m%d"):
        try:
            shift_date = datetime.strptime(
                str(current_shift.get("date") or "").strip(), date_format
            ).date()
            break
        except ValueError:
            continue
    return shift_date == production_day_key(moment)


def force_production_day_reset(moment=None):
    global last_sent_hour
    moment = moment or datetime.now()
    boundary_time = moment.replace(
        hour=PRODUCTION_DAY_BOUNDARY_HOUR, minute=0, second=0, microsecond=0
    )
    buffered_from = parse_shift_entry_datetime(shift_entry_window_started_at)
    if (
        current_shift.get("shift_id") == "NO PROD"
        and shift_entry_window_is_active(moment)
        and buffered_from == boundary_time
    ):
        return
    preserve_day_shift = (
        str(current_shift.get("shift", "")).strip().upper() == "DAY"
        and current_shift_matches_production_day(moment)
    )
    print("\n[SYSTEM] 08:00 production-day boundary reached. Resetting counters.")
    if preserve_day_shift:
        reset_production_runtime_counters()
        clear_shift_entry_window()
        last_sent_hour = moment.hour
        checkpoint_runtime_state(force=True, reason="08:00 production-day reset")
        print("[SYSTEM] Today's Day shift form was preserved.")
    else:
        reset_shift_data()
        start_shift_entry_window(boundary_time)
        print("[SYSTEM] Waiting up to 45 minutes for the Day shift form.")


def reset_stale_shift_after_startup(moment=None):
    moment = moment or datetime.now()
    if (
        current_shift.get("shift_id") != "NO PROD"
        and not current_shift_matches_production_day(moment)
    ):
        scheduled_end = get_current_shift_end_datetime()
        if scheduled_end is not None and moment >= scheduled_end:
            execute_end_shift(
                hour_slot_override=hour_slot_for_shift_end(scheduled_end),
                end_reason="MISSED SCHEDULED SHIFT END RECOVERED AT STARTUP",
            )
            start_shift_entry_window(scheduled_end)
        else:
            reset_shift_data()
        return True
    return False

def execute_end_shift(hour_slot_override=None, end_reason="MANUAL SHIFT END"):
    ending_shift_id = current_shift.get("shift_id", "NO PROD")
    if ending_shift_id == "NO PROD":
        print("\n[EVENT] No active shift. Resetting background state only.")
        reset_shift_data()
        return
    print("\n[EVENT] End Shift Triggered!")
    if (
        hourly_output != 0
        or base_time_this_hour >= 0.5
        or lost_time_this_hour >= 0.5
        or hourly_rest_time >= 0.5
    ):
        push_hourly_to_sheets(
            is_model_change=False,
            hour_slot_override=hour_slot_override,
            reason_override=f"{end_reason} FINALIZATION",
        )
    ending_event = {
        "shift_id": ending_shift_id,
        "line_code": LINE_CODE,
        "model": current_shift.get("model"),
        "lot_number": current_shift.get("lot_number"),
        "scheduled_end_at": current_shift.get("scheduled_end_at"),
        "shift_total_output": shift_total_output,
        "model_total_output": total_output,
        "total_rejects": total_rejects,
        "end_reason": end_reason,
        "ended_at": datetime.now().astimezone().isoformat(),
    }
    reset_shift_data(save_checkpoint=False)
    checkpoint_and_queue_event("shift.ended", ending_event, shift_id=ending_shift_id)
    google_sheets_queue.append({"action": "GENERATE_PDF", "shift_id": ending_shift_id})
    print(f"[GOOGLE QUEUE] PDF generation queued for Shift: {ending_shift_id}.")

def push_hourly_to_sheets(
    is_model_change=False,
    hour_slot_override=None,
    reason_override=None,
):
    global hourly_output, lost_time_this_hour, base_time_this_hour, total_output
    global hourly_rest_time, batch_run_time, real_operating_time
    global mf_count, waterjet_1_count, waterjet_2_count

    std_cycle = current_shift.get("standard_cycle", 1.0)
    base_minutes = base_time_this_hour / 60.0
    lost_minutes = lost_time_this_hour / 60.0
    available_minutes = max(0.0, base_minutes - lost_minutes)

    plan_output = int(available_minutes / std_cycle) if std_cycle > 0 else 0
    now = datetime.now()

    if hour_slot_override:
        h_slot = hour_slot_override
        reason = reason_override or "SHIFT END FINALIZATION"
    elif is_model_change:
        h_slot = get_hour_slot(now)
        reason = reason_override or "MODEL CHANGE OVERRIDE"
    else:
        end_hour = now.hour
        start_hour = (end_hour - 1) % 24
        h_slot = f"{start_hour}.00-{end_hour}.00"
        reason = reason_override or "STANDARD HOURLY PUSH"

    rest_mins = round(hourly_rest_time / 60.0, 2)

    row_data = [
        current_shift["shift_id"], current_shift["date"], current_shift["model"],
        h_slot, plan_output, hourly_output, current_shift["lot_number"], rest_mins
    ]

    print(f"\n[EVENT - HOURLY CALCULATION] Reason: {reason}")
    print(f" +--> Slot: {h_slot} | Base Mins: {base_minutes:.2f} | Lost Mins: {lost_minutes:.2f} | Available: {available_minutes:.2f}")
    print(f" +--> Target: {plan_output} | Actual: {hourly_output} | Hourly Rest: {rest_mins}m")
    print(f" +--> QUEUING DATA: {row_data}")

    google_sheets_queue.append({"tab": "Hourly_Data", "row": row_data})

    hourly_event = {
        "shift_id": current_shift["shift_id"],
        "date": current_shift["date"],
        "line": current_shift["line"],
        "shift": current_shift["shift"],
        "model": current_shift["model"],
        "hour_slot": h_slot,
        "plan": plan_output,
        "actual": hourly_output,
        "lot_number": current_shift["lot_number"],
        "rest_time": rest_mins,
        "rest_time_unit": "minutes",
        "reason": reason,
        "finalized_at": datetime.now().astimezone().isoformat()
    }
    try:
        mqtt_client.publish(
            MQTT_TOPIC_LIVE_HOURLY,
            json.dumps(hourly_event),
            qos=1
        )
        print(f"[MQTT] Published finalized hourly row to '{MQTT_TOPIC_LIVE_HOURLY}'.")
    except Exception as e:
        print(f"[MQTT ERROR] Failed to publish finalized hourly row: {e}")

    hourly_output = 0
    lost_time_this_hour = 0.0
    base_time_this_hour = 0.0
    hourly_rest_time = 0.0

    if is_model_change:
        print("[EVENT] Model Change Flag triggered -> Resetting Total Output and Real Operating Time to 0.")
        total_output = 0
        mf_count = 0
        waterjet_1_count = 0
        waterjet_2_count = 0
        batch_run_time = 0.0
        real_operating_time = 0.0

    checkpoint_and_queue_event("hourly.finalized", hourly_event)

# ==========================================
# MQTT CALLBACKS
# ==========================================
def on_connect(client, userdata, flags, rc):
    client.subscribe([(MQTT_TOPIC_SHIFT_FORM, 0), (MQTT_TOPIC_SETUP, 0),
                      (MQTT_TOPIC_NR_REJECT, 0), (MQTT_TOPIC_NR_DOWNTIME, 0),
                      (MQTT_TOPIC_NR_ENDSHIFT, 0), (MQTT_TOPIC_MODE, 0),
                      (MQTT_TOPIC_PARAM_CONDITION, 0),
                      (MQTT_TOPIC_ADJUST_COUNT, 0)])
    client.publish(
        MQTT_TOPIC_STATUS,
        json.dumps({
            "line_code": LINE_CODE,
            "status": "ONLINE",
            "recovered_from_sqlite": recovered_from_sqlite,
            "timestamp": datetime.now().astimezone().isoformat(),
        }),
        qos=1,
        retain=True,
    )
    print("\n[SYSTEM] Connected to MQTT Broker. Ready to receive commands.")

def on_message(client, userdata, msg):
    global current_mode, current_shift, total_rejects
    global hourly_output, total_output, shift_total_output, current_cycle_time

    topic = msg.topic

    try:
        payload_str = msg.payload.decode('utf-8').strip()
        try:
            data = json.loads(payload_str)
            is_json = True
        except ValueError:
            data = payload_str
            is_json = False

        if topic == MQTT_TOPIC_SHIFT_FORM and is_json:
            expire_shift_entry_window()
            previous_shift_details = dict(current_shift)
            previous_shift_id = current_shift.get("shift_id", "NO PROD")
            date_clean = data.get("prodDate", "").replace("-", "")
            new_shift_id = f"{date_clean}-{data.get('shift', '')}-{data.get('productionLine', '').replace(' ', '')}"
            if previous_shift_id != "NO PROD" and previous_shift_id != new_shift_id:
                print(
                    "[SHIFT WARNING] A different shift is already active. "
                    "The form was rejected to preserve its counters."
                )
                return
            adopting_shift_buffer = (
                previous_shift_id == "NO PROD" and shift_entry_window_is_active()
            )

            def parse_ops(op_data):
                if isinstance(op_data, list):
                    return ", ".join(op_data)
                return str(op_data) if op_data else "-"

            current_shift.update({
                "shift_id": new_shift_id,
                "date": data.get("prodDate", "-"),
                "line": data.get("productionLine", "-"),
                "shift": data.get("shift", "-"),
                "group": data.get("group", "-"),
                "workingTime": data.get("workingTime", "-"),
                "overtime": coerce_bool(data.get("overtime", False)),
                "supervisor": data.get("supervisor", "-"),
                "leader": data.get("lineLeader", "-"),
                "forming": parse_ops(data.get("formingOperator")),
                "waterjet": parse_ops(data.get("waterjetOperator")),
                "assembly": parse_ops(data.get("assemblyOperator")),
                "quality": data.get("qualityOperator", "-")
            })

            try:
                scheduled_end = calculate_shift_end_datetime(
                    current_shift["date"],
                    current_shift["shift"],
                    current_shift["overtime"],
                    current_shift["workingTime"],
                )
                if scheduled_end <= datetime.now():
                    raise ValueError(
                        f"calculated shift end {scheduled_end.isoformat()} is already past"
                    )
                current_shift["scheduled_end_at"] = scheduled_end.isoformat()
                print(
                    "[SCHEDULE] Shift will automatically end at "
                    f"{scheduled_end.strftime('%Y-%m-%d %I:%M %p')}."
                )
            except ValueError as exc:
                current_shift = previous_shift_details
                print(f"[SHIFT ERROR] Shift form rejected: {exc}")
                return

            if adopting_shift_buffer:
                clear_shift_entry_window()
                print("[SHIFT BUFFER] Buffered production assigned without reset.")

            print(f"\n[MQTT EVENT] New Shift Started: {current_shift['shift_id']}")
            row_data = [
                current_shift["shift_id"], current_shift["date"], current_shift["line"],
                current_shift["shift"], current_shift["group"], current_shift["workingTime"],
                current_shift["supervisor"], current_shift["leader"],
                current_shift["forming"], current_shift["waterjet"],
                current_shift["assembly"], current_shift["quality"]
            ]
            print(f" +--> QUEUING SHIFT DATA: {row_data}")
            google_sheets_queue.append({"tab": "Shift_Data", "row": row_data})
            checkpoint_and_queue_event(
                "shift.updated" if previous_shift_id == new_shift_id else "shift.started",
                {
                    "line_code": LINE_CODE,
                    "source_shift_id": new_shift_id,
                    "shift": dict(current_shift),
                    "source_payload": data,
                },
                event_id=data.get("event_id"),
            )

        elif topic == MQTT_TOPIC_SETUP and is_json:
            print("\n[MQTT EVENT] Setup / Model Target Updated")
            if "model" in data:
                current_shift["model"] = data.get("model", "-")
            if "lot_number" in data:
                current_shift["lot_number"] = data.get("lot_number", "-")
            if "hourly_plan" in data:
                current_shift["target"] = data.get("hourly_plan", 0)
            elif "total_target" in data:
                current_shift["target"] = data.get("total_target", 0)
            if "standard_cycle" in data:
                current_shift["standard_cycle"] = float(data.get("standard_cycle", 1.0))
            print(f" +--> Current Model: {current_shift['model']} | Lot: {current_shift['lot_number']} | Cycle: {current_shift['standard_cycle']}")
            if current_shift["shift_id"] != "NO PROD":
                checkpoint_and_queue_event(
                    "model.configured",
                    {
                        "shift_id": current_shift["shift_id"],
                        "line_code": LINE_CODE,
                        "model": current_shift["model"],
                        "lot_number": current_shift["lot_number"],
                        "target": current_shift["target"],
                        "standard_cycle": current_shift["standard_cycle"],
                        "source_payload": data,
                    },
                    event_id=data.get("event_id"),
                )
            else:
                checkpoint_runtime_state(force=True, reason="model setup without active shift")

        elif topic == MQTT_TOPIC_NR_REJECT and is_json:
            print("\n[MQTT EVENT] Reject Data Received")
            new_dashboard_rejects = safe_int(data.get("totalRejectNG"))
            total_rejects += new_dashboard_rejects

            row_data = [
                current_shift["shift_id"], get_hour_slot(),
                data.get("totalSlabReject", ""), data.get("slabRejectCode", ""),
                data.get("totalReturnRoll", ""), data.get("ohtNumber", ""),
                data.get("totalRejectNG", ""), data.get("ngRejectCode", ""),
                data.get("totalLoftLayerReject", ""), data.get("loftLayerRejectCode", "")
            ]
            print(f" +--> QUEUING REJECT: {row_data} | Running Total Rejects (Dashboard): {total_rejects}")
            google_sheets_queue.append({"tab": "Reject_Data", "row": row_data})
            if current_shift["shift_id"] != "NO PROD":
                checkpoint_and_queue_event(
                    "reject.recorded",
                    {
                        "shift_id": current_shift["shift_id"],
                        "line_code": LINE_CODE,
                        "hour_slot": get_hour_slot(),
                        "ng_quantity": data.get("totalRejectNG", ""),
                        "source_payload": data,
                    },
                    event_id=data.get("event_id"),
                )
            else:
                checkpoint_runtime_state(force=True, reason="reject without active shift")

        elif topic == MQTT_TOPIC_NR_DOWNTIME and is_json:
            print("\n[MQTT EVENT] Downtime Data Received")
            if current_mode != MODE_NORMAL:
                print(f"\n[STATE CHANGE] Downtime logged. Auto-reverting mode: {current_mode} -> {MODE_NORMAL}")
                current_mode = MODE_NORMAL

            row_data = [
                current_shift["shift_id"], get_hour_slot(),
                data.get("category", ""), data.get("code", ""),
                data.get("durationMinutes", ""), data.get("description", ""), data.get("remarks", "")
            ]
            print(f" +--> QUEUING DOWNTIME: {row_data}")
            google_sheets_queue.append({"tab": "Downtime_Data", "row": row_data})
            if current_shift["shift_id"] != "NO PROD":
                checkpoint_and_queue_event(
                    "downtime.recorded",
                    {
                        "shift_id": current_shift["shift_id"],
                        "line_code": LINE_CODE,
                        "hour_slot": get_hour_slot(),
                        "category": data.get("category", ""),
                        "code": data.get("code", ""),
                        "duration_minutes": data.get("durationMinutes", ""),
                        "description": data.get("description", ""),
                        "remarks": data.get("remarks", ""),
                    },
                    event_id=data.get("event_id"),
                )

        elif topic == MQTT_TOPIC_NR_ENDSHIFT:
            if isinstance(data, dict):
                is_end = data.get("value", False)
            else:
                is_end = data

            if is_end == True or str(is_end).lower() == "true":
                print("\n[MQTT EVENT] End Shift Requested from Node-RED!")
                execute_end_shift()

        elif topic == MQTT_TOPIC_PARAM_CONDITION and is_json:
            print("\n[MQTT EVENT] Parameter Condition Data Received")

            param_data = data.get("paramData", [{}])[0] if data.get("paramData") else {}
            temp_data = data.get("tempData", [{}])[0] if data.get("tempData") else {}
            glue_data = data.get("glueData", [{}])[0] if data.get("glueData") else {}

            model = param_data.get("model") or current_shift["model"]
            row_data = [
                current_shift["shift_id"], model,
                param_data.get("heating", ""), param_data.get("cooling", ""),
                param_data.get("shuttle", ""), param_data.get("waterjet", ""),
                temp_data.get("rh", ""), temp_data.get("ctr", ""), temp_data.get("lh", ""),
                glue_data.get("std", ""), glue_data.get("act", "")
            ]

            print(f" +--> QUEUING PARAMETER DATA: {row_data}")
            google_sheets_queue.append({"tab": "Parameter_Data", "row": row_data})
            if current_shift["shift_id"] != "NO PROD":
                checkpoint_and_queue_event(
                    "parameter.recorded",
                    {
                        "shift_id": current_shift["shift_id"],
                        "line_code": LINE_CODE,
                        "model": model,
                        "source_payload": data,
                    },
                    event_id=data.get("event_id"),
                )

        elif topic == MQTT_TOPIC_MODE:
            new_mode = str(data).upper()
            valid_modes = [MODE_NORMAL, MODE_DOWN, MODE_MODEL_CHANGE, MODE_REST, MODE_PLANNED_STOP]
            if new_mode in valid_modes:
                if new_mode == MODE_MODEL_CHANGE and current_mode != MODE_MODEL_CHANGE:
                    print("\n[EVENT] Model Change sequence initiated! Forcing hourly push...")
                    push_hourly_to_sheets(is_model_change=True)

                if current_mode != new_mode:
                    print(f"\n[STATE CHANGE] Machine Mode changed: {current_mode} -> {new_mode}")
                    current_mode = new_mode
                    checkpoint_runtime_state(force=True, reason="machine mode change")

        elif topic == MQTT_TOPIC_ADJUST_COUNT and is_json:
            adjust_val = safe_int(data.get("adjust", 0))
            print(f"\n[MQTT EVENT] Manual Count Adjustment Received: {adjust_val}")

            hourly_output = max(0, hourly_output + adjust_val)
            total_output = max(0, total_output + adjust_val)
            shift_total_output = max(0, shift_total_output + adjust_val)
            current_cycle_time = (
                (batch_run_time / total_output) / 60.0
                if total_output > 0 else 0.0
            )

            print(f" +--> Corrected Counts -> Hourly: {hourly_output} | Total: {total_output} | Shift: {shift_total_output}")
            if current_shift["shift_id"] != "NO PROD":
                checkpoint_and_queue_event(
                    "count.adjusted",
                    {
                        "shift_id": current_shift["shift_id"],
                        "line_code": LINE_CODE,
                        "adjustment": adjust_val,
                        "hourly_output_after": hourly_output,
                        "model_output_after": total_output,
                        "shift_output_after": shift_total_output,
                        "source_payload": data,
                    },
                    event_id=data.get("event_id"),
                )
            else:
                checkpoint_runtime_state(force=True, reason="count adjustment without active shift")

    except Exception as e:
        print(f"\n[ERROR] MQTT parsing failed: {e} | Payload: {msg.payload}")

restore_runtime_state()
reset_stale_shift_after_startup()

mqtt_client = mqtt.Client()
mqtt_client.on_connect = on_connect
mqtt_client.on_message = on_message
mqtt_client.will_set(
    MQTT_TOPIC_STATUS,
    json.dumps({"line_code": LINE_CODE, "status": "OFFLINE"}),
    qos=1,
    retain=True,
)
mqtt_client.connect(MQTT_BROKER, MQTT_PORT, 60)
mqtt_client.loop_start()
if outbox_sender is not None:
    outbox_sender.start()

# ==========================================
# MAIN EXECUTION LOOP
# ==========================================
def process_gsheets_queue():
    if len(google_sheets_queue) > 0:
        item = google_sheets_queue.pop(0)
        request_id = item.setdefault("request_id", str(uuid.uuid4()))
        if item.get("action") == "GENERATE_PDF":
            payload = {
                "action": "GENERATE_PDF",
                "shift_id": item["shift_id"],
                "request_id": request_id,
            }
            description = f"PDF generation for {item['shift_id']}"
        else:
            payload = {
                "action": "APPEND_ROW",
                "tab_name": item["tab"],
                "row_data": item["row"],
                "request_id": request_id,
            }
            description = f"{item['tab']} data"
        print(f"\n[HTTP] Attempting Google action: {description}...")
        try:
            response = requests.post(WEB_APP_URL, json=payload, timeout=15)
            response.raise_for_status()
            try:
                response_body = response.json()
            except ValueError as exc:
                raise RuntimeError(
                    f"Apps Script returned non-JSON response: {response.text[:200]}"
                ) from exc
            if response_body.get("status") != "success":
                raise RuntimeError(f"Apps Script rejected the request: {response_body}")
            print(f"[HTTP] SUCCESS! Completed Google action: {description}.")
        except Exception as e:
            print(f"[HTTP ERROR] Failed to send. Re-queuing action. Error: {e}")
            google_sheets_queue.insert(0, item)

def publish_live_data():
    global last_live_snapshot_publish

    standard_cycle = current_shift.get("standard_cycle", 1.0)
    live_base_minutes = base_time_this_hour / 60.0
    live_lost_minutes = lost_time_this_hour / 60.0
    live_available_minutes = max(0.0, live_base_minutes - live_lost_minutes)
    live_plan = (
        int(live_available_minutes / standard_cycle)
        if standard_cycle > 0 else 0
    )
    full_hour_plan = int(60.0 / standard_cycle) if standard_cycle > 0 else 0

    payload = {
        "shift_id": current_shift["shift_id"],
        "hour_slot": get_hour_slot(),
        "line": current_shift["line"],
        "date": current_shift["date"],
        "shift": current_shift["shift"],
        "group": current_shift["group"],
        "working_time": current_shift["workingTime"],
        "overtime": current_shift.get("overtime", False),
        "scheduled_end_at": current_shift.get("scheduled_end_at"),
        "supervisor": current_shift["supervisor"],
        "leader": current_shift["leader"],
        "forming_operator": current_shift["forming"],
        "waterjet_operator": current_shift["waterjet"],
        "assembly_operator": current_shift["assembly"],
        "quality_inspector": current_shift["quality"],
        "model": current_shift["model"],
        "lot_number": current_shift["lot_number"],
        "hourly_plan": current_shift.get("target", 0),
        "machine_status": current_status,
        "current_mode": current_mode,

        "mf_count": mf_count,
        "waterjet_1_count": waterjet_1_count,
        "waterjet_2_count": waterjet_2_count,
        "product_count": total_output,
        "total_product_count": shift_total_output,
        "hourly_output": hourly_output,
        "live_plan": live_plan,
        "full_hour_plan": full_hour_plan,
        "hour_base_minutes": round(live_base_minutes, 2),
        "hour_lost_minutes": round(live_lost_minutes, 2),
        "hour_available_minutes": round(live_available_minutes, 2),
        "total_reject": total_rejects,
        "recovered_from_sqlite": recovered_from_sqlite,
        "shift_entry_status": (
            "WAITING_FOR_SHIFT" if shift_entry_window_is_active() else
            ("ACTIVE" if current_shift["shift_id"] != "NO PROD" else "NO_PROD")
        ),
        "shift_entry_window_ends_at": shift_entry_window_ends_at,

        "current_cycle_time": round(current_cycle_time, 2),
        "standard_cycle_time": current_shift.get("standard_cycle", 1.0),

        "real_operating_time": round(real_operating_time, 2),
        "total_real_operating_time": round(total_real_operating_time, 2),
        "run_time": round(run_time, 2),
        "loading_time": round(loading_time, 2),
        "delay_time": round(delay_time, 2),
        "downtime": round(downtime, 2),
        "total_rest_time": round(total_rest_time, 2),
        "hourly_rest_time": round(hourly_rest_time, 2),
        "planned_stop_time": round(planned_stop_time, 2),
        "model_change_time": round(model_change_time, 2),
        "total_machine_time": round(total_machine_time, 2)
    }
    try:
        mqtt_client.publish(MQTT_TOPIC_DATA, json.dumps(payload))

        now = time.time()
        if now - last_live_snapshot_publish >= 1.0:
            mqtt_client.publish(
                MQTT_TOPIC_LIVE_SNAPSHOT,
                json.dumps(payload),
                qos=1,
                retain=True
            )
            last_live_snapshot_publish = now
    except Exception as e:
        print(f"[MQTT ERROR] Failed to publish live data: {e}")
    return payload

print("=====================================================")
print("  PRS Production Tracker Started (Sendayan Line 2)")
print("=====================================================")

last_loop_time = time.time()
last_debug_print_time = time.time()
last_production_day = production_day_key(datetime.now())

try:
    while True:
        current_time = time.time()
        loop_delta = current_time - last_loop_time
        last_loop_time = current_time

        now = datetime.now()
        expire_shift_entry_window(now)

        scheduled_shift_end = get_current_shift_end_datetime()
        if scheduled_shift_end is not None and now >= scheduled_shift_end:
            execute_end_shift(
                hour_slot_override=hour_slot_for_shift_end(scheduled_shift_end),
                end_reason="SCHEDULED SHIFT END",
            )
            start_shift_entry_window(scheduled_shift_end)
            continue

        current_production_day = production_day_key(now)
        if current_production_day != last_production_day:
            force_production_day_reset(now)
            last_production_day = current_production_day
            continue

        # 1. Check for Standard Hourly Push (at minute 00)
        if (
            current_shift["shift_id"] != "NO PROD"
            and now.minute == 0
            and now.hour != last_sent_hour
        ):
            push_hourly_to_sheets(is_model_change=False)
            last_sent_hour = now.hour

        # 2. Process Data Queue
        process_gsheets_queue()

        # 3. State & Timer Logic (same Sendayan formulas, lifecycle-gated)
        active_shift = current_shift.get("shift_id") != "NO PROD"
        buffering_shift_entry = shift_entry_window_is_active(now)
        production_tracking_enabled = active_shift or buffering_shift_entry
        production_loop_delta = loop_delta if production_tracking_enabled else 0.0
        base_time_this_hour += production_loop_delta
        total_machine_time += production_loop_delta

        # Only increment real operating time in NORMAL or DOWN modes
        if current_mode in [MODE_NORMAL, MODE_DOWN]:
            real_operating_time += production_loop_delta
            total_real_operating_time += production_loop_delta

        if current_mode == MODE_NORMAL:
            batch_run_time += production_loop_delta

            # [SDY2 WATERJET COUNT] Separate output event for each waterjet machine.
            # Do not add MF events to finished product counters.
            monotonic_now = time.monotonic()
            wj1_event = waterjet_1_input.poll_press(monotonic_now)
            wj2_event = waterjet_2_input.poll_press(monotonic_now)
            mf_event = mf_input.poll_press(monotonic_now)

            if production_tracking_enabled:
                new_products = int(wj1_event) + int(wj2_event)
                if wj1_event:
                    waterjet_1_count += 1
                if wj2_event:
                    waterjet_2_count += 1
                if new_products:
                    hourly_output += new_products
                    total_output += new_products
                    shift_total_output += new_products
                    current_cycle_time = (batch_run_time / total_output) / 60.0
                    checkpoint_runtime_state(force=True, reason="waterjet product detection")
                    print(f"[WATERJET] WJ1={waterjet_1_count} WJ2={waterjet_2_count} Product={total_output} Shift={shift_total_output}")

                if mf_event and monotonic_now - last_mf_event_time >= MF_MIN_EVENT_INTERVAL_SECONDS:
                    mf_count += 1
                    last_mf_event_time = monotonic_now
                    checkpoint_runtime_state(force=True, reason="MF limit-switch detection")
                    print(f"[MF] Limit switch output: {mf_count}")

            # [SDY2 MACHINE STATUS] Keep SDY2's original 90-second loading/delay rule.
            current_machine_state = get_stable_machine_state()
            if current_machine_state == 1:
                if not sensor_blocked:
                    sensor_blocked = True
                    blockage_start_time = current_time
                duration = current_time - blockage_start_time
                if duration < 90:
                    current_status = STATUS_LOADING
                    loading_time += production_loop_delta
                else:
                    current_status = STATUS_DELAY
                    delay_time += production_loop_delta
            else:
                sensor_blocked = False
                current_status = STATUS_RUN
                run_time += production_loop_delta

        else:
            if current_mode == MODE_DOWN:
                current_status = STATUS_DOWN
                downtime += production_loop_delta
                lost_time_this_hour += production_loop_delta
            elif current_mode == MODE_REST:
                current_status = STATUS_REST
                total_rest_time += production_loop_delta
                hourly_rest_time += production_loop_delta
                lost_time_this_hour += production_loop_delta
            elif current_mode == MODE_PLANNED_STOP:
                current_status = STATUS_PLANNED_STOP
                planned_stop_time += production_loop_delta
                lost_time_this_hour += production_loop_delta
            elif current_mode == MODE_MODEL_CHANGE:
                current_status = STATUS_MODEL_CHANGE
                model_change_time += production_loop_delta
                lost_time_this_hour += production_loop_delta

        if current_mode != MODE_NORMAL:
            monotonic_now = time.monotonic()
            waterjet_1_input.poll_press(monotonic_now)
            waterjet_2_input.poll_press(monotonic_now)
            mf_input.poll_press(monotonic_now)

        if buffering_shift_entry:
            current_status = STATUS_WAITING_FOR_SHIFT

        if current_status != previous_status:
            status_names = {0: "RUN", 1: "LOADING", 2: "DELAY", 3: "REST", 4: "DOWN", 5: "PLANNED STOP", 6: "MODEL CHANGE", 7: "WAITING FOR SHIFT"}
            print(f"\n[STATE CHANGE] Sensor/Machine Status changed: {status_names.get(previous_status)} -> {status_names.get(current_status)}")
            previous_status = current_status

        checkpoint_runtime_state(reason="timer checkpoint")
        live_payload = publish_live_data()

        if current_time - last_debug_print_time >= 3.0:
            print(f"\n--- [LIVE TELEMETRY @ {datetime.now().strftime('%H:%M:%S')}] ---")
            print(f"Mode: {current_mode} | Status Code: {current_status}")
            print(f"Output -> WJ1: {waterjet_1_count} | WJ2: {waterjet_2_count} | MF: {mf_count} | Hourly: {hourly_output} | Model Total: {total_output} | Shift Total: {shift_total_output}")
            print(f"Cycles -> Current: {current_cycle_time:.2f}m | Standard: {current_shift.get('standard_cycle', 1.0)}m | Rejects: {total_rejects}")
            print(
                f"Timers -> Real Op Time: {real_operating_time:.1f}s | "
                f"Total Real Op Time: {total_real_operating_time:.1f}s | "
                f"Run: {run_time:.1f}s | Load: {loading_time:.1f}s | Down: {downtime:.1f}s"
            )
            print("---------------------------------------")
            last_debug_print_time = current_time

        time.sleep(0.05)

except KeyboardInterrupt:
    print("\n\n[SYSTEM] Keyboard Interrupt Detected. Shutting down gracefully...")
finally:
    checkpoint_runtime_state(force=True, reason="graceful shutdown")
    try:
        mqtt_client.publish(
            MQTT_TOPIC_STATUS,
            json.dumps({
                "line_code": LINE_CODE,
                "status": "OFFLINE",
                "timestamp": datetime.now().astimezone().isoformat(),
            }),
            qos=1,
            retain=True,
        )
    except Exception:
        pass
    if outbox_sender is not None:
        outbox_sender.stop()
        if outbox_sender.is_alive():
            outbox_sender.join(timeout=6.0)
    GPIO.cleanup()
    mqtt_client.disconnect()
    mqtt_client.loop_stop()
    if persistence_store is not None:
        persistence_store.close()
    print("[SYSTEM] Exit complete.")
