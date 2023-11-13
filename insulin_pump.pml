#define TIME_SCALE 3
#define CLOCK_SPEED 1
#define SECOND_TO_MILLISECOND 1000
#define MINUTE_TO_MILLISECOND 60 * SECOND_TO_MILLISECOND
#define HOUR_TO_MILLISECOND 60 * MINUTE_TO_MILLISECOND

#define RESET_TIME 24 * HOUR_TO_MILLISECOND * TIME_SCALE

#define MIN_BLOOD_SUGAR 1
#define MAX_BLOOD_SUGAR 40

#define MAX_SINGLE_DOSE 4
#define MAX_DAILY_DOSE 25

#define MINIMUM_DOSE 1

#define SAFE_MIN 6
#define SAFE_MAX 14

#define INSULIN_CAPACITY 20

int clock_ms
byte blood_sugar = SAFE_MIN;

// insulin reservoir
byte insulin_available = INSULIN_CAPACITY;

// insulin pump
chan dose_to_pump = [0] of {byte};
chan dose_to_display = [0] of {byte};
byte delivered_dose;
byte cumDose = 0;

// system status
// mtype = {RUNNING, ERROR, WARNING};
mtype = {NO_INSULIN, INSULIN_LOW, SENSOR_FAIL, BATTERY_LOW};
mtype = {SUGAR_LOW, SUGAR_HIGH, SUGAR_OK};
chan status = [16] of {mtype};

active proctype clock_proc()
{
  do
    :: clock_ms == RESET_TIME -> 
      clock_ms = 0;
      cumDose = 0;
      printf("Resetting clock"); 
    :: else -> clock_ms = clock_ms + CLOCK_SPEED;
  od
}

inline split_two_digit(num, d1, d2)
{
  if
    :: num < 10 -> d1 = 0; d2 = num;
    :: else -> d1 = num/10; d2 = num%10;
  fi
}

inline get_current_time_digits(h1, h2, m1, m2, s1, s2)
{
  byte hour = clock_ms/(HOUR_TO_MILLISECOND * TIME_SCALE);
  split_two_digit(hour, h1, h2);

  byte minute = (clock_ms - hour * HOUR_TO_MILLISECOND * TIME_SCALE)/(MINUTE_TO_MILLISECOND * TIME_SCALE);
  split_two_digit(minute, m1, m2);

  byte second = (clock_ms - hour * HOUR_TO_MILLISECOND * TIME_SCALE - minute * MINUTE_TO_MILLISECOND * TIME_SCALE)/(SECOND_TO_MILLISECOND * TIME_SCALE);
  split_two_digit(second, s1, s2);
}

inline INFO()
{
  byte h1, h2, m1, m2, s1, s2;
  get_current_time_digits(h1, h2, m1, m2, s1, s2);

  printf("[%d%d:%d%d:%d%d][INFO] ", h1, h2, m1, m2, s1, s2);
}

inline WARN()
{
  byte h1, h2, m1, m2, s1, s2;
  get_current_time_digits(h1, h2, m1, m2, s1, s2);

  printf("[%d%d:%d%d:%d%d][WARNING] ", h1, h2, m1, m2, s1, s2);
}

inline ERR()
{
  byte h1, h2, m1, m2, s1, s2;
  get_current_time_digits(h1, h2, m1, m2, s1, s2);

  printf("[%d%d:%d%d:%d%d][ERROR] ", h1, h2, m1, m2, s1, s2);
}

inline rate_sleep(rate, curr_time, prev_time)
{
  atomic {
    do
      :: curr_time - prev_time >= rate -> prev_time = curr_time; break;
      :: curr_time < prev_time -> prev_time = prev_time - RESET_TIME;
    od
  }
}

inline min(lhs, a, b)
{
  if
    :: a < b -> lhs = a;
    :: else -> lhs = b;
  fi
}


inline max(lhs, a, b)
{
  if
    :: a > b -> lhs = a;
    :: else -> lhs = b;
  fi
}

inline clamp(lhs, rhs, min_value, max_value)
{
  if
    :: rhs < min_value -> lhs = min_value;
    :: rhs > max_value -> lhs = max_value;
    :: else -> lhs = rhs;
  fi
}


inline setUp(r0, r1, r2, out_dose)
{
  r0 = 0;
  r1 = SAFE_MIN;
  r2 = SAFE_MAX;
  out_dose = 0;
}

inline sugar_low(r0, r1, r2, out_dose)
{
  r2 < SAFE_MIN;
  out_dose = 0;
  // warning: Sugar low
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

active proctype controller()
{
  byte compDose;
  int prev_time = clock_ms;
  int r0, r1, r2;
  setUp(r0, r1, r2, compDose);

  do
    :: rate_sleep(10 * MINUTE_TO_MILLISECOND * TIME_SCALE, clock_ms, prev_time);
      // update blood sugar
      r0 = r1;
      r1 = r2;
      r2 = blood_sugar;

      if
        :: insulin_available >= MAX_SINGLE_DOSE &&
          cumDose < MAX_DAILY_DOSE -> 
          atomic { INFO(); printf("Controller has run for 10 minutes\n"); }
          atomic { INFO(); printf("Blood level: %d\n", blood_sugar); }
          if
            :: sugar_low(r0, r1, r2, compDose) ->
              atomic { WARN(); printf("Sugar level is low.\n"); }
            :: sugar_ok(r0, r1, r2, compDose) ->
              atomic { INFO(); printf("Sugar level is ok.\n"); }
            :: sugar_high(r0, r1, r2, compDose) ->
              atomic { ERR(); printf("Sugar level is high.\n"); }
          fi

          // send dose to pump
          dose_to_pump!compDose;
          // send dose to display
          dose_to_display!compDose;  
          
          if
            :: insulin_available <= MAX_SINGLE_DOSE * 4 -> status!INSULIN_LOW;
            :: else -> skip;
          fi            
        
          atomic { INFO(); printf("Insulin available: %d\n", insulin_available); }
        :: else -> printf("Exceed cum dose or insulin low");
      fi
  od
}

active proctype insulin_pump_proc()
{
  byte dose;
  do 
    :: dose_to_pump?dose ->
      delivered_dose = delivered_dose + dose;
      cumDose = cumDose + dose;

      insulin_available = insulin_available - dose;
  od
}

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

active proctype self_test_unit()
{
  int prev_time = clock_ms;

  do
    :: rate_sleep(30 * SECOND_TO_MILLISECOND * TIME_SCALE, clock_ms, prev_time);
      atomic { INFO(); printf("Self test has run for 30 seconds\n"); }
  od
}

// display 1 -> State error or normal
// display 2 -> dose ammount
active proctype display_dose(){
  byte dose;
  do
    :: dose_to_display?dose ->
      atomic { INFO(); printf("Dose: %d\n", dose); }
  od
}

// active proctype display_status(){
//   mtype status;
//   do
//     :: status?SUGAR_LOW -> atomic { INFO(); printf("Sugar level is low.\n"); }
//     :: else -> skip;
//   od
// }

// TODO 
// RESET

// sensor fail
// batery low
// insulin removed
// insulin low