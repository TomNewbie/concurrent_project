#define RATE 1

#define SECOND_TO_MILLISECOND 1000
#define MINUTE_TO_MILLISECOND 60 * SECOND_TO_MILLISECOND
#define HOUR_TO_MILLISECOND 60 * MINUTE_TO_MILLISECOND

#define RESET_TIME 24 * HOUR_TO_MILLISECOND * RATE

#define MIN_BLOOD_SUGAR 1
#define MAX_BLOOD_SUGAR 40

#define MAX_SINGLE_DOSE 4
#define MAX_DAILY_DOSE 25

#define MINIMUM_DOSE 1

#define SAFE_MIN 6
#define SAFE_MAX 14

#define INSULIN_CAPACITY 100

int clock_ms
byte blood_sugar = SAFE_MIN;

byte insulin_available = INSULIN_CAPACITY;
byte insulin_amount;

mtype = {SUGAR_LOW};
chan status = [0] of {mtype};

active proctype clock_proc()
{
  do
    :: clock_ms == RESET_TIME -> clock_ms = 0; printf("reset clock");
    :: else -> clock_ms++;
  od
}

inline split_time_digit(time, d1, d2)
{
  if
    :: time < 10 -> d1 = 0; d2 = time;
    :: else -> d1 = time/10; d2 = time%10;
  fi
}

inline LOG_INIT()
{
  byte hour = clock_ms/(HOUR_TO_MILLISECOND * RATE);
  byte hour1, hour2;
  split_time_digit(hour, hour1, hour2);

  byte minute = (clock_ms - hour * HOUR_TO_MILLISECOND * RATE)/(MINUTE_TO_MILLISECOND * RATE);
  byte minute1, minute2;
  split_time_digit(minute, minute1, minute2);

  byte second = (clock_ms - hour * HOUR_TO_MILLISECOND * RATE - minute * MINUTE_TO_MILLISECOND * RATE)/(SECOND_TO_MILLISECOND * RATE);
  byte second1, second2;
  split_time_digit(second, second1, second2);

  printf("[%d%d:%d%d:%d%d] ", hour1, hour2, minute1, minute2, second1, second2);
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

inline sugar_high(r0, r1, r2, dose)
{
  r2 > SAFE_MAX;
  
  if
    // sugar level increasing. Round down if below 1 unit
    :: r2 > r1 ->
      max(compDose, (r2 - r1)/4, MINIMUM_DOSE);
    // sugar level stable
    :: (r2 == r1) -> compDose = MINIMUM_DOSE;
    // sugar level falling and rate of decrease increasing
    :: (r2 <= r1 && (r2 - r1 <= r1 - r0)) -> compDose = 0;
    // sugar level falling and rate of decrease decreasing
    :: else -> compDose = MINIMUM_DOSE;
  fi
}

active proctype controller()
{
  byte compDose;
  int prev_time = clock_ms;
  int r0, r1, r2;
  byte cumDose = 0;
  setUp(r0, r1, r2, compDose);

  do
    :: rate_sleep(10 * MINUTE_TO_MILLISECOND * RATE, clock_ms, prev_time);
      // update blood sugar
      r0 = r1;
      r1 = r2;
      r2 = blood_sugar;

      if
        :: insulin_available >= MAX_SINGLE_DOSE &&
          cumDose < MAX_DAILY_DOSE -> 
          atomic { LOG_INIT(); printf("Controller has run for 10 minutes\n"); }
          atomic { LOG_INIT(); printf("Blood level: %d\n", blood_sugar); }
          if
            :: sugar_low(r0, r1, r2, compDose) ->
              atomic { LOG_INIT(); printf("Sugar level is low. Dose=%d\n", compDose); }
            :: sugar_ok(r0, r1, r2, compDose) ->
              atomic { LOG_INIT(); printf("Sugar level is ok. Dose=%d\n", compDose); }
            :: sugar_high(r0, r1, r2, compDose) ->
              atomic { LOG_INIT(); printf("Sugar level is high. Dose=%d\n", compDose); }
          fi

          // send dose to pump
          insulin_amount = insulin_amount + compDose;
          cumDose = cumDose + compDose;
          insulin_available = insulin_available - compDose;

          if
            :: insulin_available <= MAX_SINGLE_DOSE * 4 -> printf("Insulin low");
            :: else -> skip;
          fi            
          
          atomic { LOG_INIT(); printf("Insulin available: %d\n", insulin_available); }
        :: else -> printf("Exceed cum dose or insulin low");
      fi
  od
}

active proctype blood_sugar_proc()
{
  int prev_time = clock_ms;
  int v, a;

  do
  :: rate_sleep(MINUTE_TO_MILLISECOND * RATE, clock_ms, prev_time);

    if
      :: insulin_amount > 0 ->
        // insulin effect
        a = -3;
        insulin_amount--;
        clamp(v, v + a, -3, 1);
      :: else ->
        // natural blood sugar flow
        select(a: 0..4);
        a = a - 2;
        clamp(v, v + a, -1, 3);
    fi

    clamp(blood_sugar, blood_sugar + v, MIN_BLOOD_SUGAR, MAX_BLOOD_SUGAR);
    // max single dose
    atomic { LOG_INIT(); printf("Blood sugar level: %d, v=%d, a=%d\n", blood_sugar, v, a); }
	od
}

active proctype self_test_unit()
{
  int prev_time = clock_ms;

  do
    :: rate_sleep(30 * SECOND_TO_MILLISECOND * RATE, clock_ms, prev_time);
      atomic { LOG_INIT(); printf("Self test has run for 30 seconds\n"); }
  od
}


// active proctype display_dose(){
//    do
//       :: dose?insulin_amount;
//          atomic { LOG_INIT(); printf("Dose: %d\n", insulin_amount); }
//    od
// }