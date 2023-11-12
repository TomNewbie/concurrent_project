int clock_ms
int blood_sugar;
byte blood_array[3];

#define RATE 100
#define M_SECONDS_PER_HOUR 3600000
#define M_SECONDS_PER_MINUTE 60000
#define MIN_BLOOD_SUGAR 1
#define MAX_BLOOD_SUGAR 24

active proctype clock_proc()
{    
    do
        :: clock_ms == M_SECONDS_PER_HOUR * 24 * RATE -> clock_ms = 0; printf("reset clock");
        :: else -> clock_ms++
    od
}

inline rate_sleep(rate, curr_time, prev_time)
{
    atomic {
        curr_time - prev_time >= rate -> prev_time = curr_time;
    }
}

inline sugar_ok()
{
    blood_array[0] = blood_array[1];
    blood_array[1] = blood_array[2];
    blood_array[2] = blood_sugar;
    if
        :: blood_array[0] == blood_array[1] && blood_array[1] == blood_array[2] ->
            printf("Sugar level is stable\n");
            blood_channel!blood_sugar;
        :: else -> skip;
    fi
}

inline sugar_high()
{
    blood_array[0] = blood_array[1];
    blood_array[1] = blood_array[2];
    blood_array[2] = blood_sugar;
    if
        :: blood_array[0] == blood_array[1] && blood_array[1] == blood_array[2] ->
            printf("Sugar level is high\n"); 
            blood_channel!blood_sugar;
        :: else -> skip;
    fi
}

inline sugar_low()
{
    blood_array[0] = blood_array[1];
    blood_array[1] = blood_array[2];
    blood_array[2] = blood_sugar;
    if
        :: blood_array[0] == blood_array[1] && blood_array[1] == blood_array[2] ->
            printf("Sugar level is low\n");
            blood_channel!blood_sugar;
        :: else -> skip;
    fi
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

// inline clamp(lhs, rhs, min, max)
// {
//     if
//         :: rhs < min -> lhs = min;
//         :: rhs > max -> lhs = max;
//         :: else -> lhs = rhs;
//     fi
// }

inline hehe(a, b, c, d)
{
    if
        :: b < c -> a = c;
        :: b > d -> a = d;
        :: else -> a = b;
    fi
}

active proctype controller()
{
    int prev_time = 0;
    int curr_time;

    do
        :: curr_time = clock_ms;
        if
            :: curr_time - prev_time >= 1000 * 60 * 10 * RATE->
                printf("Controller has run for 10 minutes\n");
                printf("Blood level: %d\n", blood_sugar);
                prev_time = curr_time; 
            :: else -> if
                :: curr_time < prev_time -> prev_time = 0;
                :: else -> skip;
                fi
        fi
    od
}

active proctype blood_sugar_proc()
{
    int prev_time = clock_ms;
    int v, a;

    do
    :: rate_sleep(1000 * 10 * RATE, clock_ms, prev_time);
    
        select(a: 0..4);
        a = a - 2;

        clamp(v, v + a, -1, 5);
        
        clamp(blood_sugar, blood_sugar + v, MIN_BLOOD_SUGAR, MAX_BLOOD_SUGAR);
    
        // max single dose
        printf("Blood sugar level: %d, v=%d, a=%d\n", blood_sugar, v, a);
	od
}

active proctype self_test_unit()
{
    int prev_time = 0
    int curr_time;

    do
        :: curr_time = clock_ms;
        if
            :: curr_time - prev_time >= 1000 * 30 * RATE->
                printf("Self test has run for 30 seconds\n");
                prev_time = curr_time;
            :: else -> if
                :: curr_time < prev_time -> prev_time = 0;
                :: else -> skip;
                fi
        fi
    od
}

active proctype display_time(){
    byte hour = 0;
    byte minute = 0;

    int curr_clock_ms; 
    int prev_clock_ms = 0;
    do
        :: curr_clock_ms = clock_ms;
        if
            :: curr_clock_ms - prev_clock_ms >= 1000 * 60 * RATE ->
                minute++;
                hour = minute/60;
                prev_clock_ms = curr_clock_ms;
                printf("Current time: %d:%d\n", hour%24, minute%60)
            :: else -> skip;
        fi
    od
}