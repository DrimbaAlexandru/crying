mtype = { userCame, userLeft, waterStarted, waterStopped }

chan signal_user_to_tap = [0] of { mtype };
chan signal_tap_to_user = [0] of { mtype };

bool waterRunning = false;
bool usingTap = false;

byte tapTimer = 0;
byte userTimer = 0;
    
active proctype WaterTap() 
{
    end:
    do
    /* If water is not running and a user came, start the water tap and start the timer. */
    ::  waterRunning == false ->
        atomic 
        { 
        signal_user_to_tap ? userCame ->
            printf( "User came\n" ); 
            waterRunning = true;
            tapTimer = 10;
            signal_tap_to_user ! waterStarted
        }
    
    :: waterRunning == true ->
        /* If water is running and the user leaves, stop the water and reset the timer */
        if
        ::  atomic {
                signal_user_to_tap ? userLeft ->
                    waterRunning = false;
                    tapTimer = 0
                    /* no need to send a waterStopped signal here, because the user already left */
                }
                
        /* If water is running and the user has not left yet, decrease the timer. If timer is 0, stop the water and notify the user */
        :: else ->
            atomic {
                if 
                :: tapTimer > 0 -> 
                    tapTimer--
                :: else -> 
                    waterRunning = false;
                    if
                    :: signal_tap_to_user ! waterStopped -> skip
                    :: signal_user_to_tap ? userLeft -> skip
                    fi
                fi
                }
        fi
    od
}       

active proctype User() 
{   
    end:
    do
    /* A new user starts using the tap */
    ::  usingTap == false ->
        atomic 
        {
            userTimer = 1;
            
            do
            :: userTimer < 20 -> userTimer++
            :: userTimer <= 20 -> break
            od;
            
            usingTap = true;
            signal_user_to_tap ! userCame;
            signal_tap_to_user ? waterStarted;
            printf( "Start using the tap\n" );
        }
    :: usingTap == true ->
        {
        if
        /* If the water stops, the user leaves */
        ::  atomic 
            {
                signal_tap_to_user ? waterStopped ->
                    printf( "The water has stopped\n" );
                    usingTap = false;
                    userTimer = 0
            }
        :: else ->
        /* If the water is still running, choose whether to stay or to leave */
            atomic
            {
                if 
                :: userTimer > 0 -> userTimer--
                :: userTimer == 0 -> 
                    usingTap = false; 
                    if
                    :: signal_user_to_tap ! userLeft -> skip
                    :: signal_tap_to_user ? waterStopped -> skip
                    fi
                fi
            }
        fi
        }
    od;        
}

/* Water will eventually stop running */
/* ltl { []( waterRunning == true -> <>( waterRunning == false ) ) } */

/* When the user stops using the tap, the water will eventually stop */
/* ltl { []( usingTap == false -> <>( waterRunning == false ) ) } */

/* Tap timer never goes out of bounds */
/* ltl { []( tapTimer >= 0 && tapTimer <= 10 ) } */

/* Water runs until the user leaves or the timer elapses */
ltl { []( ( waterRunning == true ) U ( tapTimer == 0 ||  usingTap == false ) ) }