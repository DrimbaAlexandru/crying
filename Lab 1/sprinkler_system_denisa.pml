mtype = { startWatering, stopWatering, moistureChanged }

chan moistureSignal = [0] of { mtype, int };
chan sprinklerSignal = [0] of { mtype };

bool sprinklerWatering = false;  /*  The initial state of the sprinkler is stopped */

int currentMoistureValue = 50;

active proctype Controller() {
    int newMoistureValue;
    do
        :: moistureSignal ?? moistureChanged, newMoistureValue -> {
            printf("Received signal for moisture change: %d\n", newMoistureValue);
            if 
                :: newMoistureValue >= 80 -> atomic { 
					sprinklerSignal ! stopWatering
 				}
                :: newMoistureValue <= 40 -> atomic {
					sprinklerSignal ! startWatering
				}
				:: else -> printf("No action neccessary\n")
            fi;
        }
    od
}

active proctype Sprinkler() {
    do
        :: sprinklerSignal ?? startWatering -> atomic {
            printf("Received signal to start watering \n");
            sprinklerWatering = true;
        }
		:: sprinklerSignal ?? stopWatering -> atomic {
            printf("Received signal to stop watering \n");
            sprinklerWatering = false;
        }
    od
}

active proctype SoilMoistureSensor() {
    moistureIncreasing: 
        do
            :: sprinklerWatering == true && currentMoistureValue + 20 <= 100 -> atomic { 
                currentMoistureValue = currentMoistureValue + 20; 
                moistureSignal!moistureChanged(currentMoistureValue)
            }
			:: sprinklerWatering == true && currentMoistureValue + 20 > 100 -> atomic {
				currentMoistureValue = 100; 
                moistureSignal!moistureChanged(currentMoistureValue)
			}
            :: else -> goto moistureDecreasing
        od;

    moistureDecreasing:
        do
            :: sprinklerWatering == false && currentMoistureValue - 20 >= 0 -> atomic {
                currentMoistureValue = currentMoistureValue - 20;
                moistureSignal!moistureChanged(currentMoistureValue);
            }
			:: sprinklerWatering == false && currentMoistureValue - 20 < 0 -> atomic {
                currentMoistureValue = 0;
                moistureSignal!moistureChanged(currentMoistureValue);
            }
            :: else -> goto moistureIncreasing
        od;
}


ltl p1 { [](0 <= currentMoistureValue && currentMoistureValue <= 100) }

//ltl p2 { ( currentMoistureValue <= 40 -> <>( sprinklerWatering == true ) ) }

//ltl p3 { []( currentMoistureValue >= 80 -> <>( sprinklerWatering == false ) ) }