int clock_ms
byte blood_level;
chan blood_channel = [0] of {byte};
byte blood_array[3];
chan controller_hasRun = [0] of {byte};

proctype clock_proc()
{    
    do
        :: clock_ms++
    od
}

inline sugar_ok()
{
    blood_array[0] = blood_array[1];
    blood_array[1] = blood_array[2];
    blood_array[2] = blood_level;
    if
        :: blood_array[0] == blood_array[1] && blood_array[1] == blood_array[2] ->
            printf("Sugar level is stable\n");
            blood_channel!blood_level;
        :: else -> skip;
    fi
}

inline sugar_high()
{
    blood_array[0] = blood_array[1];
    blood_array[1] = blood_array[2];
    blood_array[2] = blood_level;
    if
        :: blood_array[0] == blood_array[1] && blood_array[1] == blood_array[2] ->
            printf("Sugar level is high\n");
            blood_channel!blood_level;
        :: else -> skip;
    fi
}

inline sugar_low()
{
    blood_array[0] = blood_array[1];
    blood_array[1] = blood_array[2];
    blood_array[2] = blood_level;
    if
        :: blood_array[0] == blood_array[1] && blood_array[1] == blood_array[2] ->
            printf("Sugar level is low\n");
            blood_channel!blood_level;
        :: else -> skip;
    fi
}

proctype controller()
{
    int prev_time = 0
    int curr_time;

    do
        :: curr_time = clock_ms;
        if
            :: curr_time - prev_time >= 1000 * 60 * 200 ->
                printf("Controller has run for 200 minutes\n");
                printf("Blood level: %d\n", blood_level);
                prev_time = curr_time;
            :: else -> skip;
        fi
    od
}

proctype sensor()
{
    do
    ::if
        :: blood_level > 100 -> sugar_high();
        :: blood_level < 50 -> sugar_low();
        :: else -> sugar_ok();
    fi
	:: blood_level++	;
	:: blood_level--	;	

	od;
}

proctype self_test()
{
    int prev_time = 0
    int curr_time;

    do
        :: curr_time = clock_ms;
        if
            :: curr_time - prev_time >= 1000 * 60 * 10 ->
                printf("Self test has run for 10 minutes\n");
                prev_time = curr_time;
            :: else -> skip;
        fi
    od
}

init {
    run clock_proc();
    run controller();
    run self_test();
    run sensor();
}