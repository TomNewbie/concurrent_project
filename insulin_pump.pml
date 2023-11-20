// Increase the clock speed for faster simulation
#define CLOCK_SPEED 2

// Increase the time scale for slower simulation
#define TIME_SCALE 1

// Time units
#define SECOND_TO_MILLISECOND 1000
#define MINUTE_TO_MILLISECOND 60 * SECOND_TO_MILLISECOND
#define HOUR_TO_MILLISECOND 60 * MINUTE_TO_MILLISECOND

#define RESET_TIME 24 * HOUR_TO_MILLISECOND * TIME_SCALE

// Blood sugar level
#define MIN_BLOOD_SUGAR 1
#define MAX_BLOOD_SUGAR 40
#define SAFE_MIN 6
#define SAFE_MAX 14

// Insulin computation
#define MAX_SINGLE_DOSE 4
#define MAX_DAILY_DOSE 25
#define MINIMUM_DOSE 1

// Hardware configuration
#define INSULIN_CAPACITY 20
#define LOW_BATTERY_LEVEL 10



/*
 * Global variables
 */

int clock_ms

// blood sugar reading
byte blood_sugar = SAFE_MIN;

/*
 * Insulin computation
 */
byte cumDose = 0;
chan dose_to_pump = [0] of {byte};
byte delivered_dose = 0;

/*
 * System status
 */
mtype = {RUNNING, ERROR, WARNING};
mtype system_status = RUNNING;

// Warning types
mtype = {SUGAR_LOW, INSULIN_LOW};
// Error types
mtype = {NO_INSULIN, SENSOR_FAIL, BATTERY_LOW, EXCEED_CUM_DOSE};

/*
 * Displays
 */
chan display1 = [0] of {mtype};
chan display2 = [0] of {mtype};

/*
 * Hardware variables
 */
byte battery_level = 100;
bool sensor_failed = false;
chan external_error_handling = [2] of {mtype};

bool is_reservoir_present = true;
byte insulin_available = INSULIN_CAPACITY;



/*
 * Utility inline definitions
 */

// set lhs to the minimum of a and b
inline min(lhs, a, b)
{
  if
  :: a < b -> lhs = a;
  :: else -> lhs = b;
  fi
}

// set lhs to the maximum of a and b
inline max(lhs, a, b)
{
  if
  :: a > b -> lhs = a;
  :: else -> lhs = b;
  fi
}

// clamp the lhs value between min_value and max_value
inline clamp(lhs, rhs, min_value, max_value)
{
  if
  :: rhs < min_value -> lhs = min_value;
  :: rhs > max_value -> lhs = max_value;
  :: else -> lhs = rhs;
  fi
}



/*
 * Clock
 */

// Simulate the system's clock
active proctype clock_proc()
{
  do
  :: int c = clock_ms + CLOCK_SPEED;
    if
    :: c < RESET_TIME -> clock_ms = c;
    :: else -> atomic {
      clock_ms = c % RESET_TIME;
      cumDose = 0;
      printf("[INFO] Resetting clock");
    }
    fi
  od
}

// Simulate a process sleeping for a given rate
inline rate_sleep(rate, curr_time, prev_time)
{
  atomic {
    do
    // block until the elapsed time is greater than the rate
    :: curr_time - prev_time >= rate -> prev_time = curr_time; break;
    // roll back if the clock has been reset
    :: curr_time < prev_time -> prev_time = prev_time - RESET_TIME;
    od
  }
}



/*
 * Logging
 */

// Split a two digit number into two digits
inline split_two_digit(num, d1, d2)
{
  if
  :: num < 10 -> d1 = 0; d2 = num;
  :: else -> d1 = num/10; d2 = num%10;
  fi
}

// Get the current time in separate digits
inline get_current_time_digits(h1, h2, m1, m2, s1, s2)
{
  byte hour = clock_ms/(HOUR_TO_MILLISECOND * TIME_SCALE);
  split_two_digit(hour, h1, h2);

  byte minute = (clock_ms - hour * HOUR_TO_MILLISECOND * TIME_SCALE)/(MINUTE_TO_MILLISECOND * TIME_SCALE);
  split_two_digit(minute, m1, m2);

  byte second = (clock_ms - hour * HOUR_TO_MILLISECOND * TIME_SCALE - minute * MINUTE_TO_MILLISECOND * TIME_SCALE)/(SECOND_TO_MILLISECOND * TIME_SCALE);
  split_two_digit(second, s1, s2);
}

// Header for an info log
inline INFO()
{
  byte h1, h2, m1, m2, s1, s2;
  get_current_time_digits(h1, h2, m1, m2, s1, s2);

  printf("[%d%d:%d%d:%d%d][INFO] ", h1, h2, m1, m2, s1, s2);
}

// Header for a warning log
inline WARN()
{
  byte h1, h2, m1, m2, s1, s2;
  get_current_time_digits(h1, h2, m1, m2, s1, s2);

  printf("[%d%d:%d%d:%d%d][WARNING] ", h1, h2, m1, m2, s1, s2);
}

// Header for an error log
inline ERR()
{
  byte h1, h2, m1, m2, s1, s2;
  get_current_time_digits(h1, h2, m1, m2, s1, s2);

  printf("[%d%d:%d%d:%d%d][ERROR] ", h1, h2, m1, m2, s1, s2);
}



/*
 * Main controller - insulin computation
 */

inline sugar_low(r0, r1, r2, out_dose)
{
  r2 < SAFE_MIN;
  out_dose = 0;

  display1!SUGAR_LOW;
}

inline sugar_ok(r0, r1, r2, out_dose)
{
  r2 >= SAFE_MIN && r2 <= SAFE_MAX;

  if
  // sugar level stable or falling
  :: r2 <= r1 ->
    out_dose = 0;
  // sugar level increasing but rate of increase falling
  :: r2 > r1 && (r2 - r1) < (r1 - r0) ->
    out_dose = 0
  // sugar level increasing and rate of increase increasing compute dose
  // a minimum dose must be delivered if rounded to zero
  :: r2 > r1 && (r2 - r1) >= (r1 - r0) ->
    max(out_dose, (r2 - r1) / 4, MINIMUM_DOSE)
  fi
}

inline sugar_high(r0, r1, r2, out_dose)
{
  r2 > SAFE_MAX;
  
  if
  // sugar level increasing. Round down if below 1 unit
  :: r2 > r1 ->
    max(out_dose, (r2 - r1)/4, MINIMUM_DOSE);
  // sugar level stable
  :: (r2 == r1) -> out_dose = MINIMUM_DOSE;
  // sugar level falling and rate of decrease increasing
  :: (r2 <= r1 && (r2 - r1 <= r1 - r0)) -> out_dose = 0;
  // sugar level falling and rate of decrease decreasing
  :: else -> out_dose = MINIMUM_DOSE;
  fi
}

inline run_insulin_computation(r0, r1, r2)
{
  // guard
  system_status != ERROR &&
  insulin_available >= MAX_SINGLE_DOSE &&
  cumDose < MAX_DAILY_DOSE;

  atomic { INFO(); printf("Running insulin computation...\n"); }
  
  byte compDose;

  // compute the insulin dose
  if
  :: sugar_low(r0, r1, r2, compDose);
  :: sugar_ok(r0, r1, r2, compDose);
  :: sugar_high(r0, r1, r2, compDose);
  fi
  
  clamp(compDose, compDose, 0, MAX_SINGLE_DOSE);

  if
  // The maximum daily dose would be exceeded if the computed dose was delivered
  :: compDose + cumDose > MAX_DAILY_DOSE ->
    system_status = WARNING;
    compDose = MAX_DAILY_DOSE - cumDose;
  :: else -> skip;
  fi

  // Send dose to pump
  dose_to_pump!compDose;

  insulin_available = insulin_available - compDose;
  cumDose = cumDose + compDose;
  
  if
  :: insulin_available <= MAX_SINGLE_DOSE * 4 ->
    system_status = WARNING;
    display1!INSULIN_LOW;
  :: else -> skip;
  fi

  atomic { INFO(); printf("Insulin available: %d\n", insulin_available); }
}

active proctype controller()
{
  int prev_time = clock_ms;
  int r0, r1, r2;

  is_reservoir_present = true;
  insulin_available = INSULIN_CAPACITY;

  r0 = 0;
  r1 = SAFE_MIN;
  r2 = SAFE_MAX;

  do
  :: rate_sleep(10 * MINUTE_TO_MILLISECOND * TIME_SCALE, clock_ms, prev_time);
    // update blood sugar
    r0 = r1;
    r1 = r2;
    r2 = blood_sugar;
    
    if
    :: run_insulin_computation(r0, r1, r2);
    :: else -> atomic { ERR(); printf("Cannot run insulin computation\n"); }
    fi
  od
}



/*
 * Insulin pump simulation
 */

// Simulate pump delivery
active proctype insulin_pump_proc()
{
  byte dose;
  
  do 
  :: dose_to_pump?dose ->
    delivered_dose = delivered_dose + dose;
    display2!dose;
  od
}

// Simulate blood sugar level of patient
active proctype blood_sugar_proc()
{
  int prev_time = clock_ms;
  int v, a;

  do
  :: rate_sleep(MINUTE_TO_MILLISECOND * TIME_SCALE, clock_ms, prev_time);

    if
    :: delivered_dose > 0 ->
      // insulin effect
      a = -3;
      delivered_dose--;
      clamp(v, v + a, -3, 1);
    :: else ->
      // natural blood sugar flow
      select(a: 0..4);
      a = a - 2;
      clamp(v, v + a, -1, 3);
    fi
    
    clamp(blood_sugar, blood_sugar + v, MIN_BLOOD_SUGAR, MAX_BLOOD_SUGAR);
    
    atomic { INFO(); printf("Blood sugar level: %d, v=%d, a=%d\n", blood_sugar, v, a); }
	od
}



/*
 * Self test unit
 */

inline run_error_tests(out_is_error)
{
  out_is_error = false;

  if
  :: battery_level <= LOW_BATTERY_LEVEL ->
    out_is_error = true;
    display1!BATTERY_LOW;
    
    external_error_handling!BATTERY_LOW;
  :: else -> skip;
  fi
  
  if
  :: is_reservoir_present && insulin_available < MAX_SINGLE_DOSE ->
    out_is_error = true;
    display1!NO_INSULIN;
    
    external_error_handling!NO_INSULIN;
  :: else -> skip;
  fi

  if
  :: cumDose > MAX_DAILY_DOSE ->
    out_is_error = true;
    display1!EXCEED_CUM_DOSE;
  :: else -> skip;
  fi

  if
  :: sensor_failed ->
    out_is_error = true;
    display1!SENSOR_FAIL;
  :: else -> skip;
  fi
}

active proctype self_test_unit()
{
  int prev_time = clock_ms;

  do
  :: rate_sleep(30 * SECOND_TO_MILLISECOND * TIME_SCALE, clock_ms, prev_time);
    atomic { INFO(); printf("Running self test...\n"); }

    bool is_error;
    run_error_tests(is_error);

    if
    :: is_error -> system_status = ERROR;
    :: else -> system_status = RUNNING;
    fi
  od
}



/*
 * External error handling simulation
 */

// Simulate battery drain
active proctype battery_proc()
{
  int prev_time = clock_ms;

  do
  :: rate_sleep(1 * HOUR_TO_MILLISECOND * TIME_SCALE, clock_ms, prev_time);
    clamp(battery_level, battery_level - 1, 0, 100);
  od
}

// Simulate battery replacement
active proctype replace_battery_proc()
{
  do
  :: external_error_handling?BATTERY_LOW ->
    atomic { INFO(); printf("Replacing the battery...\n"); }
    
    battery_level = 100;
  od
}

// Simulate reservoir replacement
active proctype replace_reservoir_proc()
{
  do
  :: external_error_handling?NO_INSULIN ->
    atomic { INFO(); printf("Replacing the insulin reservoir...\n"); }

    is_reservoir_present = false;
    insulin_available = INSULIN_CAPACITY;
    is_reservoir_present = true;
  od
}



/*
 * Displays simulations
 */

active proctype display_status()
{
  do
  :: display1?SUGAR_LOW -> atomic { WARN(); printf("Sugar low\n"); }
  :: display1?INSULIN_LOW -> atomic { WARN(); printf("Insulin low\n"); }
  :: display1?EXCEED_CUM_DOSE -> atomic { ERR(); printf("Daily dose exceeded\n"); }
  :: display1?NO_INSULIN -> atomic { ERR(); printf("No insulin\n"); }
  :: display1?BATTERY_LOW -> atomic { ERR(); printf("Battery low\n"); }
  :: display1?SENSOR_FAIL -> atomic { ERR(); printf("Sensor failure\n"); }
  od
}

active proctype display_dose()
{
  byte dose;
  
  do
  :: display2?dose -> atomic { INFO(); printf("Insulin dose: %d\n", dose); }
  od
}
