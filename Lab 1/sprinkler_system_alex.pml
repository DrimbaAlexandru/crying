mtype = { startWatering, stopWatering, moistureChanged }

chan moistureSignal = [0] of { mtype, int };
chan sprinklerSignal = [0] of { mtype };

bool sprinklerWatering = false;

/* mocked value that would represent the information from an actual soil moisture sensor */
byte currentMoistureValue = 50;	/* start from middle` initial state */

active proctype Controller() {
	int newMoistureValue;
    
    end:
    do
        :: atomic 
        {
			moistureSignal ? moistureChanged, newMoistureValue -> 
            {
                printf("Received signal for moisture change: %d\n", newMoistureValue);
                if 
                    :: ( newMoistureValue >= 80 ) && ( sprinklerWatering == true )  -> sprinklerSignal ! stopWatering
                    :: ( newMoistureValue <= 40 ) && ( sprinklerWatering == false ) -> sprinklerSignal ! startWatering
                    :: else -> printf( "Sprinkler state needs no change\n" )
                fi;
            }
        }
    od
}

active proctype SoilMoistureSensor() {
    int prevMoistureValue = currentMoistureValue;
    
    do
        /* Simulate a non-deterministic new value for the moisture value */
        ::  atomic {
            if
                :: ( !sprinklerWatering || currentMoistureValue == 0  )  -> currentMoistureValue = 0
                :: ( !sprinklerWatering || currentMoistureValue <= 10 )  -> currentMoistureValue = 10
                :: ( !sprinklerWatering || currentMoistureValue <= 20 )  -> currentMoistureValue = 20
                :: ( !sprinklerWatering || currentMoistureValue <= 30 )  -> currentMoistureValue = 30
                :: ( !sprinklerWatering || currentMoistureValue <= 40 )  -> currentMoistureValue = 40
                :: ( !sprinklerWatering || currentMoistureValue <= 50 )  -> currentMoistureValue = 50
                :: ( !sprinklerWatering || currentMoistureValue <= 60 )  -> currentMoistureValue = 60
                :: ( !sprinklerWatering || currentMoistureValue <= 70 )  -> currentMoistureValue = 70
                :: ( !sprinklerWatering || currentMoistureValue <= 80 )  -> currentMoistureValue = 80
                :: ( !sprinklerWatering || currentMoistureValue <= 90 )  -> currentMoistureValue = 90
                :: ( !sprinklerWatering || currentMoistureValue <= 100 ) -> currentMoistureValue = 100
            fi;
            
            if
                :: prevMoistureValue != currentMoistureValue -> 
                    prevMoistureValue = currentMoistureValue;
                    moistureSignal ! moistureChanged( currentMoistureValue )
				:: else ->
                    printf( "Moisture value is the same\n" );
            fi;
            }
    od
}

active proctype Sprinkler() {
    mtype command;
    
    end:
    do
        :: atomic {
        sprinklerSignal ? command ->
            if  
                :: command == startWatering ->
                    printf("Received signal to start watering\n");
                    sprinklerWatering = true
                :: command == stopWatering ->
                    printf("Received signal to stop watering\n");
                    sprinklerWatering = false;
            fi
        }
    od
}


//ltl { []( currentMoistureValue >= 0 && currentMoistureValue <= 100 ) }

//ltl { []( currentMoistureValue <= 40 -> <>( sprinklerWatering == true ) ) }

//ltl { []( currentMoistureValue >= 80 -> <>( sprinklerWatering == false ) ) }