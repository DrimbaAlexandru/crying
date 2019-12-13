# Smart Gardner
**Smart Gardner**  is an embedded system that periodically monitors the state of a houseplant by reading sensor values from two different sensors: a soil humidity sensor and a temperature sensor. The system consists of an *Arduino Uno* development board, a *soil moisture sensor*, a *temperature sensor*, a *16x2 LCD display*, a *breadboard*, and *connectors*.

## System logic
The system’s goal is to inform its user about the houseplant’s state by using the sensor data to compute the overall state of the plant. Based on predefined thresholds for soil humidity (`HUM_THRESHOLD_*`, where * = 0, 1, 2, 3) and room temperature (`TEMP_THRESHOLD_*`, where * = 0, 1, 2, 3), the overall state can be either of the following: `HAPPY`, `OK` and `SAD`. The data from each sensor is mapped to a `BAD`/`OK`/`EXCELLENT` state (see fig. 1), and the overall state is computed as being the worse of the sensor states (i.e., if the temperature is *excellent* but the moisture is *bad*, the plant is *sad*). The overall state, the temperature and soil moisture values are all displayed on the LCD.

![Imgur](https://imgur.com/cL6CU3U.png)

![Imgur1](https://imgur.com/oSPBMGF.png)
*Fig.1. Thresholds*

## Components
For the development of the system, we used two sensors and an LCD, the use of which is described below.

### Sensors
Two sensors were used to create the system: **soil moisture sensor** and **temperature sensor**. Both implementations (*noFSM* and *withFSM*) use these sensors in the same way, with the following methods being identical:
1. `readHumidityPercentage()` reads the value of soil moisture. The values ​​determined by this sensor are between 0 (meaning maximum humidity) and 1023 (representing the lack of humidity). For later use, these values ​​were mapped to percentages (0 - 100%);
3.  `readSensorTemperature()` determines the temperature in the air on Celsius scale (°C).

In both methods, an average of 100 values ​​read by the sensor is calculated, to ensure that the value is as consistent with the reality as possible.

### LCD display
An 16x2 LCD was used to display the values ​​determined through the sensors, but also the state of the plant. For the display on this LCD were also used common methods between the two implementations.
1. `void displayHumidityAndTemp(int humidityPercentage, float temperature)`   
displays the percentage of soil moisture read by the sensor and temperature;
2. `setCustomChars()` is a method that sets custom characters for the LCD. A maximum of 8 such characters can be set on the LCD. An LCD display is made up of blocks, which are fundamentally **5** dots in a row and **8** dots in a column, which are lighted up according to the code or predefined characters inside the LCD Control IC. Such a character is described by a byte array of size 8, each element describing which of the 5 dots from a column is lit:
```
byte happy1[] = {B00000, B00110, B01001, B00000, B00000, B00000, B00000, B00000};
lcd.createChar(0, happy1);
```
4. `displayHappyEmoticon()`, `displayOkEmoticon()` and `displaySadEmoticon()` are methods that display the custom characters that form emoticons that describe the state of the plant.

## NoFSM & FSM
### NoFSM implementation
The implementation of _noFSM_ uses the specific method of the `void loop()` in which it reads the moisture for soil and temperature, calculates the final state of the plant (bad, good, excellent) and depending on the result, it is displayed properly on the LCD.
### FSM implementation
  
In the _FSM_ implementation, 4 different states are used:
1. `STATE_ACQUIRE_DATA` in which the values ​​of the sensors are read, the state of the plant is calculated and, according to this, the state of the FSM changes. This is the only state of the FSM in which there is a logic that determines the next state of the FSM.
2. `STATE_HAPPY_PLANT`, `STATE_OK_PLANT`, `STATE_SAD PLANT` are states in which the emoticon corresponding to the state of the plant and the values ​​of the sensors are displayed. After a delay of `WAIT_TIME`, the FSM returns to the` STATE_ACQUIRE_DATA` state.

Next can be seen a diagram describing the FSM:

![alt ](https://imgur.com/rIVqyE8.png)











