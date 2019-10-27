mtype = { startWatering, stopWatering, moistureChanged }

chan moistureSignal = [0] of { mtype, int };
chan sprinklerSignal = [0] of { mtype };

bool sprinklerWatering = false;

/* mocked value that would represent the information from an actual soil moisture sensor */
int currentMoistureValue = 40;

active proctype Controller() {
	int newMoistureValue;
    do
        :: moistureSignal ?? moistureChanged, newMoistureValue -> {
            printf("Received signal for moisture change: %d\n", newMoistureValue);
            if 
                :: newMoistureValue >= 80 -> sprinklerSignal ! stopWatering
                :: newMoistureValue <= 40 -> sprinklerSignal ! startWatering
				:: else -> printf("Soil value ok")
            fi;
        }
    od
}

active proctype SoilMoistureSensor() {
    int lastMoistureValue = 0;
    checkMoisture: {
        if
            :: lastMoistureValue != currentMoistureValue -> {
                lastMoistureValue = currentMoistureValue;
                moistureSignal ! moistureChanged(currentMoistureValue);
            }
        fi;
        goto checkMoisture;
    }
}

active proctype Sprinkler() {
    do
        :: sprinklerSignal ?? startWatering -> {
            printf("Received signal to start watering \n");
            sprinklerWatering = true;
            /* mocked value to simulate the increase of moisture in the soil once the sprinkler has started */
            currentMoistureValue = 86; 
        }
        :: sprinklerSignal ?? stopWatering -> {
            printf("Received signal to stop watering \n");
            sprinklerWatering = false;
            /* mocked value to simulate the decrease of moisture in the soil once the sprinkler has stopped */
            currentMoistureValue = 34;
        }
    od
}