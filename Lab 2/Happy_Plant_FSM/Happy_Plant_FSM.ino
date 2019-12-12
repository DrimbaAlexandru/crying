#include <Wire.h>
#include <LiquidCrystal_I2C.h>

#define STATE_ACQUIRE_DATA 0
#define STATE_HAPPY_PLANT 1
#define STATE_OK_PLANT 2
#define STATE_SAD_PLANT 3

#define HUM_THRESHOLD_0 30
#define HUM_THRESHOLD_1 45
#define HUM_THRESHOLD_2 65
#define HUM_THRESHOLD_3 80

#define TEMP_THRESHOLD_0 12
#define TEMP_THRESHOLD_1 18
#define TEMP_THRESHOLD_2 28
#define TEMP_THRESHOLD_3 35

#define WAIT_TIME 1000

// Define LCD pinout
const int  en = 2, rw = 1, rs = 0, d4 = 4, d5 = 5, d6 = 6, d7 = 7, bl = 3;
const int i2c_addr = 0x27;
LiquidCrystal_I2C lcd(i2c_addr, en, rw, rs, d4, d5, d6, d7, bl, POSITIVE);

int fsmState;
int humidityPin = A0;
int temperaturePin = A1;

int humidityPercentage;
float temperature;
int temperatureState, humidityState, state;

void setup() {
  Serial.begin(9600);
  fsmState = STATE_ACQUIRE_DATA;
  lcd.begin(16, 2);
  lcd.clear();
  setCustomChars();  
}

int readHumidityPercentage() {
  long sensorValue = 0;
  for(int i = 0; i < 100; i++) {
    sensorValue = sensorValue + analogRead(humidityPin);
  }
  sensorValue = sensorValue/100.0; 
  int percentage = map(sensorValue,1023,500,0,100);
  return percentage;
}

float readSensorTemperature() {
  float temperatureSum = 0;
  for (int i = 0; i < 100; i++) {
    int reading = analogRead(temperaturePin);
    float voltage = reading * 5.0;
    voltage /= 1024.0;
    float temperatureCelsius = (voltage - 0.5) * 100 ;
    temperatureSum = temperatureSum + temperatureCelsius;
  }
  return temperatureSum / (float)100;
}

int calculateState(int percentage, int t0, int t1, int t2, int t3) {
  if(percentage <= t0 || t3 <= percentage) { return 0; } 
  else if(t1 <= percentage && percentage <= t2) { return 2; } 
  else { return 1; }
}

void loop() {
  switch(fsmState) {
    case STATE_ACQUIRE_DATA:
      Serial.println("Acquiring data...");
      humidityPercentage = readHumidityPercentage();
      humidityState = calculateState(humidityPercentage, HUM_THRESHOLD_0, HUM_THRESHOLD_1, HUM_THRESHOLD_2, HUM_THRESHOLD_3);
      temperature = readSensorTemperature();
      temperatureState = calculateState(temperature, TEMP_THRESHOLD_0, TEMP_THRESHOLD_1, TEMP_THRESHOLD_2, TEMP_THRESHOLD_3);
      state = min(humidityState, temperatureState); //change when adding temp sensor
      if(state == 0) { fsmState = STATE_SAD_PLANT; } 
      else if(state == 1) { fsmState = STATE_OK_PLANT; }
      else { fsmState = STATE_HAPPY_PLANT; }
      break;
      
    case STATE_HAPPY_PLANT:
      Serial.println("Plant entered happy state...");
      displayHappyEmoticon();      
      displayHumidityAndTemp(humidityPercentage, temperature);
      delay(WAIT_TIME);
      fsmState = STATE_ACQUIRE_DATA;
      break;
      
    case STATE_OK_PLANT:
      Serial.println("Plant entered ok state...");
      displayOkEmoticon();
      displayHumidityAndTemp(humidityPercentage, temperature);
      delay(WAIT_TIME);
      fsmState = STATE_ACQUIRE_DATA;
      break;
      
    case STATE_SAD_PLANT:
      Serial.println("Plant entered sad state...");
      displaySadEmoticon();
      displayHumidityAndTemp(humidityPercentage, temperature);
      delay(WAIT_TIME);
      fsmState = STATE_ACQUIRE_DATA;
      break;
  }
}

void displayHumidityAndTemp(int humidityPercentage, float temperature) {
  String humidityString = "HUM: " + String(humidityPercentage) + "%";
  lcd.setCursor(4,0);
  lcd.print(humidityString);

  String temperatureString = "TMP: " + String(temperature);
  lcd.setCursor(4,1);
  lcd.print(temperatureString);

  lcd.setCursor(14, 1);
  lcd.print((char)223);
  lcd.setCursor(15, 1);
  lcd.print("C");
}

void displayHappyEmoticon() {
  lcd.clear();
    
  lcd.write((uint8_t)0);
  lcd.write((uint8_t)1);
  lcd.write((uint8_t)2);
}

void displayOkEmoticon() {
  lcd.clear();
  
  lcd.write((uint8_t)3);
  lcd.write((uint8_t)4);
  lcd.write((uint8_t)5);
}

void displaySadEmoticon() {
  lcd.clear();
    
  lcd.write((uint8_t)6);
  lcd.write((uint8_t)7);
  lcd.write((uint8_t)6);
}

void setCustomChars() {
  byte happy1[] = {B00000, B00110, B01001, B00000, B00000, B00000, B00000, B00000};
  byte happy2[] = {B00000, B00000, B00000, B00000, B00000, B10001, B01110, B00000};
  byte happy3[] = {B00000, B01100, B10010, B00000, B00000, B00000, B00000, B00000};
  
  byte meh1[] = {B00000, B01001, B00110, B00000, B00000, B00000, B00000, B00000};
  byte meh2[] = {B00000, B00000, B00000, B00000, B00000, B00000, B11111, B00000};
  byte meh3[] = {B00000, B10010, B01100, B00000, B00000, B00000, B00000, B00000};
  
  byte sad1[] = { B00000, B01010, B00100, B01010, B00000, B00000, B00000, B00000 };
  byte sad2[] = { B00000, B00000, B00000, B00000, B00000, B00000, B01110, B10001 };

  lcd.createChar(0, happy1);
  lcd.createChar(1, happy2);
  lcd.createChar(2, happy3);

  lcd.createChar(3, meh1);
  lcd.createChar(4, meh2);
  lcd.createChar(5, meh3);

  lcd.createChar(6, sad1);
  lcd.createChar(7, sad2);
}
