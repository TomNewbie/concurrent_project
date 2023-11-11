int clock_ms
byte blood_sugar;
byte blood_array[3];

#define RATE 1
#define M_SECONDS_PER_HOUR 3600000
#define M_SECONDS_PER_MINUTE 60000

active proctype clock_proc()
{    
    do
        :: clock_ms == M_SECONDS_PER_HOUR * 24 * RATE -> clock_ms = 0; printf("reset clock");
        :: else -> clock_ms++
    od
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

active proctype controller()
{
    int prev_time = 0
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
    do
	:: blood_sugar = blood_sugar;
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
                // printf("Current time: %02d:%02d\n", hour%24, minute%60)
            :: else -> skip;
        fi
    od
}