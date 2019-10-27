mtype = { requestAmount, garbageAmount, trashDumped, trashNeedsEmptied, trashEmptied }

chan signal_amount = [0] of { mtype, byte };
chan signal_request_amount = [0] of { mtype };
chan signal_dump_trash = [0] of { mtype }; 
chan signal_dump_emptied = [0] of { mtype }; 
chan signal_needs_empty = [0] of { mtype };

bool level_needs_update = true;
bool request_sent = false;
byte trash_level = 0;

bool will_come_to_empty = false;

active proctype Controller() {   
    byte new_garbage_level;
    
    do
        :: signal_amount ? garbageAmount, new_garbage_level -> atomic {
            printf("Received the garbage level from the sensor: %d\n", new_garbage_level);
            if 
                :: new_garbage_level >= 75 -> signal_needs_empty ! trashNeedsEmptied; 
                :: else -> printf( "Does not need to be emptied yet\n" ); will_come_to_empty = false
            fi;
            level_needs_update = false;
            request_sent = false;
            trash_level = new_garbage_level
        }
        
        :: signal_dump_trash ? trashDumped -> atomic {
            level_needs_update = true;
        }
        
        :: signal_dump_emptied ? trashEmptied -> atomic {
            trash_level = 0;
        }
        
        :: false == request_sent && true == level_needs_update ->
            printf( "Request sent to the sensor\n" );
            signal_request_amount ! requestAmount;
            request_sent = true            
    od
}

active proctype ProximitySensor() {
    byte current_amount;
    do 
        :: signal_request_amount ? requestAmount -> atomic {
            current_amount = trash_level + 40;
            signal_amount ! garbageAmount, current_amount
        }
    od
}

active proctype User() {
    do
        :: printf( "User dumps trash\n" ); signal_dump_trash ! trashDumped
    od
}

active proctype RecyclingCentre() {
    do
        :: signal_needs_empty ? trashNeedsEmptied -> 
            atomic {
                printf("Yeah sure mate, we'll come pick it up\n");
				will_come_to_empty = true;
                signal_dump_emptied ! trashEmptied
            }
    od
}

/* ltl { []( level_needs_update == true -> <>( request_sent == true ) ) } */

ltl { []( ( trash_level >= 75 ) -> <>( will_come_to_empty == true ) ) }
