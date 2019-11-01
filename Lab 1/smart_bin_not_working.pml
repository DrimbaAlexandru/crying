mtype = { requestAmount, garbageAmount, trashDumped, needsEmpty, trashPickedUp }

chan signal_amount = [0] of { mtype, byte };
chan signal_request_amount = [0] of { mtype };
chan signal_dump_trash = [0] of { mtype }; 
chan signal_needs_empty = [0] of { mtype };
chan signal_pick_up_trash = [0] of { mtype };

byte sensor_trash_level = 0;
byte real_trash_level = 0;
byte emptying = false;

bool trash_dumped = false;
bool request_sent = false;

active proctype Controller() {   
    byte new_garbage_level;

    /* get the initial garbage level */
    printf( "Request sent to the sensor\n" );
    request_sent = true;
    signal_request_amount ! requestAmount;
                            
    end:
    do
        :: atomic 
        {
			signal_amount ? garbageAmount, new_garbage_level -> 
            {
                printf("Received the garbage level from the sensor: %d\n", new_garbage_level);
                if 
                    :: ( sensor_trash_level < 75 ) && ( new_garbage_level >= 75 ) -> signal_needs_empty ! needsEmpty
                    :: ( new_garbage_level < 75 ) -> printf( "Does not need to be emptied yet\n" ); emptying = false
                    :: else -> printf( "Empty request already sent\n" );
                fi;
                request_sent = false;
                sensor_trash_level = new_garbage_level
            }
        }
        
        ::  ( false == request_sent );
            if
            :: signal_dump_trash ? trashDumped ->
                atomic {
                    printf( "Request sent to the sensor\n" );
                    request_sent = true;    
                    trash_dumped = false;                
                    signal_request_amount ! requestAmount;
                }

            :: signal_pick_up_trash ? trashPickedUp ->
                atomic {
                    printf( "Trash got picked up\n" );
                    request_sent = true;               
                    signal_request_amount ! requestAmount;
                }
            fi
    od
}

active proctype ProximitySensor() {

    do
        ::  atomic {
            signal_request_amount ? requestAmount ->
                signal_amount ! garbageAmount, real_trash_level
            }
    od
}

active proctype User() {
    
    end:
    do
        /* A user can exist only if they can add garbage to the bin, i.e. the bin is not full */
        :: atomic { 
            !emptying;
            printf( "User dumps trash\n" );
            do
              :: real_trash_level < 100 -> real_trash_level = real_trash_level + 10
              :: true -> break
            od;
            
            trash_dumped = true;
            signal_dump_trash ! trashDumped
        }
    od
}

active proctype RecyclingCentre() {
    
    end:
    do
        :: signal_needs_empty ? needsEmpty -> 
            atomic {
                printf( "Yeah sure mate, we'll come pick your shit up\n" );
                real_trash_level = 0;
                emptying = true;
                signal_pick_up_trash ! trashPickedUp
            }
    od
}
 
/* ltl { []( trash_dumped == true -> <>( request_sent == true ) ) } */

/* ltl { []( ( sensor_trash_level >= 75 ) -> <>( waiting_for_empty == true ) ) } */

