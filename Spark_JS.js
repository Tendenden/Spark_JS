var events = require('events');
var util = require('util');
var Queue = require('sync-queue');
var m = require('mraa');
var q = new Queue();

var I2C_ADDR = 0x39
  , GESTURE_THRESHOLD_OUT = 20
  , GESTURE_SENSITIVITY = 0.8//0.5
  , ENABLE = 0x80
  , ATIME = 0x81
  , WTIME = 0x83
  , AILTL = 0x84
  , AILTH = 0x85
  , AIHTL = 0x86
  , AIHTH = 0x87
  , PILT = 0x89
  , PIHT = 0x8B
  , PERS = 0x8C
  , CONFIG1 = 0x8D
  , PPULSE = 0x8E
  , CONTROL = 0x8F
  , CONFIG2 = 0x90
  , ID = 0x92
  , STATUS = 0x93
  , CDATAL = 0x94
  , CDATAH = 0x95
  , RDATAL = 0x96
  , RDATAH = 0x97
  , GDATAL = 0x98
  , GDATAH = 0x99
  , BDATAL = 0x9A
  , BDATAH = 0x9B
  , PDATA = 0x9C
  , POFFSET_UR = 0x9D
  , POFFSET_DL = 0x9E
  , CONFIG3 = 0x9F
  , GPENTH = 0xA0
  , GEXTH = 0xA1
  , GCONF1 = 0xA2
  , GCONF2 = 0xA3
  , GOFFSET_U = 0xA4
  , GOFFSET_D = 0xA5
  , GOFFSET_L = 0xA7
  , GOFFSET_R = 0xA9
  , GPULSE = 0xA6
  , GCONF3 = 0xAA
  , GCONF4 = 0xAB
  , GFLVL = 0xAE
  , GSTATUS = 0xAF
  , IFORCE = 0xE4
  , PICLEAR = 0xE5
  , CICLEAR = 0xE6
  , AICLEAR = 0xE7
  , GFIFO_U = 0xFC
  , GFIFO_D = 0xFD
  , GFIFO_L = 0xFE
  , GFIFO_R = 0xFF
  , ID_RES = 0xAB
  ;

var ERROR  =0xFF;
/* Direction definitions */
var DIR = {
  DIR_NONE :0,
  DIR_LEFT :1,
  DIR_RIGHT:2,
  DIR_UP:3,
  DIR_DOWN:4,
  DIR_NEAR:5,
  DIR_FAR:6,
  DIR_ALL:7
};

/* State definitions */
var STA = {
  NA_STATE :0,
  NEAR_STATE:1,
  FAR_STATE:2,
  ALL_STATE:3
};


/* Bit fields */
var APDS9960_PON    =         1
var APDS9960_AEN     =        1 << 1
var APDS9960_PEN      =       1 << 2
var APDS9960_WEN       =      1 << 3
var APSD9960_AIEN       =     1 << 4
var APDS9960_PIEN        =    1 << 5
var APDS9960_GEN          =   1 << 6
var APDS9960_GVALID        =  1

/* On/Off definitions */
var OFF                  =   0
var ON                    =  1

/* Acceptable parameters for setMode */
var POWER                =   0
var AMBIENT_LIGHT         =  1
var PROXIMITY              = 2
var WAIT                    =3
var AMBIENT_LIGHT_INT       =4
var PROXIMITY_INT           =5
var GESTURE                 =6
var ALL                     =7

/* LED Drive values */
var LED_DRIVE_100MA         =0
var LED_DRIVE_50MA          =1
var LED_DRIVE_25MA          =2
var LED_DRIVE_12_5MA        =3

/* Proximity Gain (PGAIN) values */
var PGAIN_1X               = 0
var PGAIN_2X                =1
var PGAIN_4X                =2
var PGAIN_8X                =3

/* ALS Gain (AGAIN) values */
var AGAIN_1X                =0
var AGAIN_4X                =1
var AGAIN_16X               =2
var AGAIN_64X               =3

/* Gesture Gain (GGAIN) values */
var GGAIN_1X                =0
var GGAIN_2X                =1
var GGAIN_4X                =2
var GGAIN_8X                =3

/* LED Boost values */
var LED_BOOST_100           =0
var LED_BOOST_150           =1
var LED_BOOST_200           =2
var LED_BOOST_300           =3    

/* Gesture wait time values */
var GWTIME_0MS              =0
var GWTIME_2_8MS            =1
var GWTIME_5_6MS            =2
var GWTIME_8_4MS            =3
var GWTIME_14_0MS           =4
var GWTIME_22_4MS           =5
var GWTIME_30_8MS           =6
var GWTIME_39_2MS           =7



// bits on the enable register
var ENABLE_GEN = 6 // gesture enable
  , ENABLE_PIEN = 5 // proximity interrupt enable
  , ENABLE_AIEN = 4 // ALS interrupt enable
  , ENABLE_WEN = 3 // wait enable. 1 = activates wait timer
  , ENABLE_PEN = 2 // proximity detect enable
  , ENABLE_AEN = 1 // ALS enable
  , ENABLE_PON = 0 // Power on. 0 = low power state
  ;

var gesture_ud_delta_ = 0;
    gesture_lr_delta_ = 0;
    
    gesture_ud_count_ = 0;
    gesture_lr_count_ = 0;
    
    gesture_near_count_ = 0;
    gesture_far_count_ = 0;
    
    gesture_state_ = 0;
    gesture_motion_ = DIR.DIR_NONE;

var APDS9960_ID_1           =0xAB;
var APDS9960_ID_2           =0x9C;

/*default value*/
var DEFAULT_ATIME           =219 ;    // 103ms
var DEFAULT_WTIME           =246  ;   // 27ms
var DEFAULT_PROX_PPULSE     =0x87  ;  // 16us, 8 pulses
var DEFAULT_GESTURE_PPULSE  =0x89   ; // 16us, 10 pulses
var DEFAULT_POFFSET_UR      =0       ;// 0 offset
var DEFAULT_POFFSET_DL      =0       ;// 0 offset      
var DEFAULT_CONFIG1         =0x60    ;// No 12x wait (WTIME) factor
var DEFAULT_LDRIVE          =LED_DRIVE_100MA;
var DEFAULT_PGAIN           =PGAIN_4X;
var DEFAULT_AGAIN           =AGAIN_4X;
var DEFAULT_PILT            =0       ;// Low proximity threshold
var DEFAULT_PIHT            =50     ; ;// High proximity threshold
var DEFAULT_AILT            =0xFFFF  ;// Force interrupt for calibration
var DEFAULT_AIHT            =0;
var DEFAULT_PERS            =0x11;    // 2 consecutive prox or ALS for var.
var DEFAULT_CONFIG2         =0x01;    // No saturation interrupts or LED boost  
var DEFAULT_CONFIG3         =0   ;    // Enable all photodiodes, no SAI
var DEFAULT_GPENTH          =40  ;    // Threshold for entering gesture mode
var DEFAULT_GEXTH           =30  ;    // Threshold for exiting gesture mode    
var DEFAULT_GCONF1          =0x40;    // 4 gesture events for var., 1 for exit
var DEFAULT_GGAIN           =GGAIN_4X;
var DEFAULT_GLDRIVE         =LED_DRIVE_100MA;
var DEFAULT_GWTIME          =GWTIME_2_8MS;
var DEFAULT_GOFFSET         =0      ; // No offset scaling for gesture mode
var DEFAULT_GPULSE          =0xC9   ; // 32us, 10 pulses
var DEFAULT_GCONF3          =0      ; // All photodiodes active during gesture
var DEFAULT_GIEN            =0      ; // Disable gesture interrupts



function  init()
{
    var id = [0];
    //var id;

    /* Initialize I2C */
    //Wire.begin();
     
    /* Read ID register and check against known values for APDS-9960 */
    if( !wireReadDataByte(I2C_ADDR, id[0]) ) {
        return false;
    }
    if( !(id[0] == APDS9960_ID_1 || id[0] == APDS9960_ID_2) ) {
        return false;
    }
     
    /* Set ENABLE register to 0 (disable all features) */
    if( !setMode(ALL, OFF) ) {
        return false;
    }
    
    /* Set default values for ambient light and proximity registers */
    if( !wireWriteDataByte(ATIME, DEFAULT_ATIME) ) {
        return false;
    }
    if( !wireWriteDataByte(WTIME, DEFAULT_WTIME) ) {
        return false;
    }
    if( !wireWriteDataByte(PPULSE, DEFAULT_PROX_PPULSE) ) {
        return false;
    }
    if( !wireWriteDataByte(POFFSET_UR, DEFAULT_POFFSET_UR) ) {
        return false;
    }
    if( !wireWriteDataByte(POFFSET_DL, DEFAULT_POFFSET_DL) ) {
        return false;
    }
    if( !wireWriteDataByte(CONFIG1, DEFAULT_CONFIG1) ) {
        return false;
    }
    if( !setLEDDrive(DEFAULT_LDRIVE) ) {
        return false;
    }
    if( !setProximityGain(DEFAULT_PGAIN) ) {
        return false;
    }
    if( !setAmbientLightGain(DEFAULT_AGAIN) ) {
        return false;
    }
    if( !setProxIntLowThresh(DEFAULT_PILT) ) {
        return false;
    }
    if( !setProxIntHighThresh(DEFAULT_PIHT) ) {
        return false;
    }
    if( !setLightIntLowThreshold(DEFAULT_AILT) ) {
        return false;
    }
    if( !setLightIntHighThreshold(DEFAULT_AIHT) ) {
        return false;
    }
    if( !wireWriteDataByte(PERS, DEFAULT_PERS) ) {
        return false;
    }
    if( !wireWriteDataByte(CONFIG2, DEFAULT_CONFIG2) ) {
        return false;
    }
    if( !wireWriteDataByte(CONFIG3, DEFAULT_CONFIG3) ) {
        return false;
    }
    
    /* Set default values for gesture sense registers */
    if( !setGestureEnterThresh(DEFAULT_GPENTH) ) {
        return false;
    }
    if( !setGestureExitThresh(DEFAULT_GEXTH) ) {
        return false;
    }
    if( !wireWriteDataByte(GCONF1, DEFAULT_GCONF1) ) {
        return false;
    }
    if( !setGestureGain(DEFAULT_GGAIN) ) {
        return false;
    }
    if( !setGestureLEDDrive(DEFAULT_GLDRIVE) ) {
        return false;
    }
    if( !setGestureWaitTime(DEFAULT_GWTIME) ) {
        return false;
    }
    if( !wireWriteDataByte(GOFFSET_U, DEFAULT_GOFFSET) ) {
        return false;
    }
    if( !wireWriteDataByte(GOFFSET_D, DEFAULT_GOFFSET) ) {
        return false;
    }
    if( !wireWriteDataByte(GOFFSET_L, DEFAULT_GOFFSET) ) {
        return false;
    }
    if( !wireWriteDataByte(GOFFSET_R, DEFAULT_GOFFSET) ) {
        return false;
    }
    if( !wireWriteDataByte(GPULSE, DEFAULT_GPULSE) ) {
        return false;
    }
    if( !wireWriteDataByte(GCONF3, DEFAULT_GCONF3) ) {
        return false;
    }
    if( !setGestureIntEnable(DEFAULT_GIEN) ) {
        return false;
    }
    
// #if 0
//     /* Gesture config register dump */
//     var reg;
//     var val;
  
//     for(reg = 0x80; reg <= 0xAF; reg++) {
//         if( (reg != 0x82) && \
//             (reg != 0x8A) && \
//             (reg != 0x91) && \
//             (reg != 0xA8) && \
//             (reg != 0xAC) && \
//             (reg != 0xAD) )
//         {
//             wireReadDataByte(reg, val);
//             console.log(reg, HEX);
//             console.log(": 0x");
//             console.log(val, HEX);
//         }
//     }

//     for(reg = 0xE4; reg <= 0xE7; reg++) {
//         wireReadDataByte(reg, val);
//         console.log(reg, HEX);
//         console.log(": 0x");
//         console.log(val, HEX);
//     }
// #endif

    return true;
}





function GestureSensor (scl,sda) {
  this.hardware = hardware;/*tessel.port[A]*/
  this.i2c = this.hardware.I2C(I2C_ADDR);

  var self = this;
  this._readRegister([ID], 1, function(err, data){
    if (data[0] != ID_RES) {
      self.emit('error', new Error('Cannot connect APDS Gesture sensor. Got id: ' + data[0].toString(16)));
    } else {
      self.fifoData = {};

      self.emit('ready');
    }
  });
}



/*******************************************************************************
 * Raw I2C Reads and Writes
 ******************************************************************************/

/**
 * @brief Writes a single byte to the I2C device (no register)
 *
 * @param[in] val the 1-byte value to write to the I2C device
 * @return True if successful write operation. False otherwise.
 */
var i2c = new m.I2c(0);
i2c.address(I2C_ADDR);

//unit8 val
function wireWriteByte(val)
{
    i2c.writeByte(val);
    return true;
    // Wire.beginTransmission(I2C_ADDR);
    // Wire.write(val);
    // if( Wire.endTransmission() != 0 ) {
    //     return false;
    // }
    
    // return true;
}

/**
 * @brief Writes a single byte to the I2C device and specified register
 *
 * @param[in] reg the register in the I2C device to write to
 * @param[in] val the 1-byte value to write to the I2C device
 * @return True if successful write operation. False otherwise.
 */
function wireWriteDataByte(reg,val)
{

    i2c.writeReg(reg,val[0]);
    // Wire.beginTransmission(APDS9960_I2C_ADDR);
    // Wire.write(reg);
    // Wire.write(val);
    // if( Wire.endTransmission() != 0 ) {
    //     return false;
    // }

    return true;
}

/**
 * @brief Writes a block (array) of bytes to the I2C device and register
 *
 * @param[in] reg the register in the I2C device to write to
 * @param[in] val pointer to the beginning of the data byte array
 * @param[in] len the length (in bytes) of the data to write
 * @return True if successful write operation. False otherwise.
 */
function wireWriteDataBlock(reg, val, len)//*val
{

    for(i = 0; i < len; i++) {
      i2c.writeReg(reg,val[i]);
    }
    // unsigned var i;

    // Wire.beginTransmission(APDS9960_I2C_ADDR);
    // Wire.write(reg);
    // for(i = 0; i < len; i++) {
    //     Wire.beginTransmission(val[i]);
    // }
    // if( Wire.endTransmission() != 0 ) {
    //     return false;
    // }

    return true;
}

/**
 * @brief Reads a single byte from the I2C device and specified register
 *
 * @param[in] reg the register to read from
 * @param[out] the value returned from the register
 * @return True if successful read operation. False otherwise.
 */
function wireReadDataByte(reg, val)//&val va[]
{
    
    val[0] = i2c.readReg(reg);
    //??? read(1)

    /* Indicate which register we want to read from */
    // if (!wireWriteByte(reg)) {
    //     return false;
    // }
    
    // /* Read from register */
    // Wire.requestFrom(APDS9960_I2C_ADDR, 1);
    // while (Wire.available()) {
    //     val = Wire.read();
    // }

    return true;
}

/**
 * @brief Reads a block (array) of bytes from the I2C device and register
 *
 * @param[in] reg the register to read from
 * @param[out] val pointer to the beginning of the data
 * @param[in] len number of bytes to read
 * @return Number of bytes read. -1 on read error.
 */
// function wireReadDataBlock(reg,val,len)//*val
// {


//     while(i <= len) {
//       val[i] = i2c.read(1);

//     }

//     unsigned char i = 0;
    
//     /* Indicate which register we want to read from */
//     if (!wireWriteByte(reg)) {
//         return -1;
//     }
    
//     /* Read block data */
//     Wire.requestFrom(APDS9960_I2C_ADDR, len);
//     while (Wire.available()) {
//         if (i >= len) {
//             return -1;
//         }
//         val[i] = Wire.read();
//         i++;
//     }

//     return i;
// }
/*******************************************************************************
 * Public methods for controlling the APDS-9960
 ******************************************************************************/

/**
 * @brief Reads and returns the contents of the ENABLE register
 *
 * @return Contents of the ENABLE register. 0xFF if error.
 */
function getMode()
{
    var enable_value = [0];
    
    /* Read current ENABLE register */
    if( !wireReadDataByte(ENABLE, enable_value) ) {
        return ERROR;
    }
    
    return enable_value[0];
}

/**
 * @brief Enables or disables a feature in the APDS-9960
 *
 * @param[in] mode which feature to enable
 * @param[in] enable ON (1) or OFF (0)
 * @return True if operation success. False otherwise.
 */
function setMode(mode,enable)
{
    var reg_val = [0];

    /* Read current ENABLE register */
    reg_val[0] = getMode();
    if( reg_val[0] == ERROR ) {
        return false;
    }
    
    /* Change bit(s) in ENABLE register */
    enable = enable & 0x01;
    if( mode >= 0 && mode <= 6 ) {
        if (enable) {
            reg_val[0] |= (1 << mode);
        } else {
            reg_val[0] &= ~(1 << mode);
        }
    } else if( mode == ALL ) {
        if (enable) {
            reg_val[0] = 0x7F;
        } else {
            reg_val[0] = 0x00;
        }
    }
        
    /* Write value back to ENABLE register */
    if( !wireWriteDataByte(ENABLE, reg_val) ) {
        return false;
    }
        
    return true;
}

/**
 * @brief Starts the light (R/G/B/Ambient) sensor on the APDS-9960
 *
 * @param[in] interrupts true to enable hardware interrupt on high or low light
 * @return True if sensor enabled correctly. False on error.
 */
function enableLightSensor(interrupts)
{
    
    /* Set default gain, interrupts, enable power, and enable sensor */
    if( !setAmbientLightGain(DEFAULT_AGAIN) ) {
        return false;
    }
    if( interrupts ) {
        if( !setAmbientLightIntEnable(1) ) {
            return false;
        }
    } else {
        if( !setAmbientLightIntEnable(0) ) {
            return false;
        }
    }
    if( !enablePower() ){
        return false;
    }
    if( !setMode(AMBIENT_LIGHT, 1) ) {
        return false;
    }
    
    return true;

}

/**
 * @brief Ends the light sensor on the APDS-9960
 *
 * @return True if sensor disabled correctly. False on error.
 */
function disableLightSensor()
{
    if( !setAmbientLightIntEnable(0) ) {
        return false;
    }
    if( !setMode(AMBIENT_LIGHT, 0) ) {
        return false;
    }
    
    return true;
}

/**
 * @brief Starts the proximity sensor on the APDS-9960
 *
 * @param[in] interrupts true to enable hardware external interrupt on proximity
 * @return True if sensor enabled correctly. False on error.
 */
function enableProximitySensor(interrupts)
{
    /* Set default gain, LED, interrupts, enable power, and enable sensor */
    if( !setProximityGain(DEFAULT_PGAIN) ) {
        return false;
    }
    if( !setLEDDrive(DEFAULT_LDRIVE) ) {
        return false;
    }
    if( interrupts ) {
        if( !setProximityIntEnable(1) ) {
            return false;
        }
    } else {
        if( !setProximityIntEnable(0) ) {
            return false;
        }
    }
    if( !enablePower() ){
        return false;
    }
    if( !setMode(PROXIMITY, 1) ) {
        return false;
    }
    
    return true;
}

/**
 * @brief Ends the proximity sensor on the APDS-9960
 *
 * @return True if sensor disabled correctly. False on error.
 */
function disableProximitySensor()
{
  if( !setProximityIntEnable(0) ) {
    return false;
  }
  if( !setMode(PROXIMITY, 0) ) {
    return false;
  }

  return true;
}

/**
 * @brief Starts the gesture recognition engine on the APDS-9960
 *
 * @param[in] interrupts true to enable hardware external interrupt on gesture
 * @return True if engine enabled correctly. False on error.
 */
function enableGestureSensor(interrupts)
{
    
    /* Enable gesture mode
       Set ENABLE to 0 (power off)
       Set WTIME to 0xFF
       Set AUX to LED_BOOST_300
       Enable PON, WEN, PEN, GEN in ENABLE 
    */
    resetGestureParameters();
    if( !wireWriteDataByte(WTIME, 0xFF) ) {
        return false;
    }
    if( !wireWriteDataByte(PPULSE, DEFAULT_GESTURE_PPULSE) ) {
        return false;
    }
    if( !setLEDBoost(LED_BOOST_300) ) {
        return false;
    }
    if( interrupts ) {
        if( !setGestureIntEnable(1) ) {
            return false;
        }
    } else {
        if( !setGestureIntEnable(0) ) {
            return false;
        }
    }
    if( !setGestureMode(1) ) {
        return false;
    }
    if( !enablePower() ){
        return false;
    }
    if( !setMode(WAIT, 1) ) {
        return false;
    }
    if( !setMode(PROXIMITY, 1) ) {
        return false;
    }
    if( !setMode(GESTURE, 1) ) {
        return false;
    }
    
    return true;
}

/**
 * @brief Ends the gesture recognition engine on the APDS-9960
 *
 * @return True if engine disabled correctly. False on error.
 */
function disableGestureSensor()
{
    resetGestureParameters();
    if( !setGestureIntEnable(0) ) {
        return false;
    }
    if( !setGestureMode(0) ) {
        return false;
    }
    if( !setMode(GESTURE, 0) ) {
        return false;
    }
    
    return true;
}

/**
 * @brief Determines if there is a gesture available for reading
 *
 * @return True if gesture available. False otherwise.
 */
function isGestureAvailable()
{
    var val = [0];
    
    /* Read value from GSTATUS register */
    if( !wireReadDataByte(GSTATUS, val) ) {
        return ERROR;
    }
    
    /* Shift and mask out GVALID bit */
    val[0] &= APDS9960_GVALID;
    
    /* Return true/false based on GVALID bit */
    if( val[0] == 1) {
        return true;
    } else {
        return false;
    }
}

/**
 * @brief Processes a gesture event and returns best guessed gesture
 *
 * @return Number corresponding to gesture. -1 on error.
 */
function readGesture()
{
    var fifo_level = [0];
    var bytes_read = [0];
    var fifo_data = new Array(128);
    var gstatus = [0]; //
    var motion = [0] //
    var i = [0]; //
    
    /* Make sure that power and gesture is on and data is valid */
    // if( !isGestureAvailable() || !(getMode() & 0b01000001) ) {
    //     return DIR.DIR_NONE;
    // }
    if( !isGestureAvailable() || !(getMode() & ((1 << 6)+1)) ) {
        return DIR.DIR_NONE;
    }
    
    /* Keep looping as long as gesture data is valid */
    while(1) {
    
        /* Wait some time to collect next batch of FIFO data */
        delay(FIFO_PAUSE_TIME);
        
        /* Get the contents of the STATUS register. Is data still valid? */
        if( !wireReadDataByte(GSTATUS, gstatus) ) {
            return ERROR;
        }
        
        /* If we have valid data, read in FIFO */
        if( (gstatus & APDS9960_GVALID) == APDS9960_GVALID ) {
        
            /* Read the current FIFO level */
            if( !wireReadDataByte(APDS9960_GFLVL, fifo_level) ) {
                return ERROR;
            }

// #if DEBUG
//             console.log("FIFO Level: ");
//             console.log(fifo_level);
// #endif

            /* If there's stuff in the FIFO, read it into our data block */
            if( fifo_level > 0) {
                bytes_read = wireReadDataBlock(  APDS9960_GFIFO_U, 
                                                fifo_data, 
                                                (fifo_level * 4) );
                if( bytes_read == -1 ) {
                    return ERROR;
                }
// #if DEBUG
//                 console.log("FIFO Dump: ");
//                 for ( i = 0; i < bytes_read; i++ ) {
//                     console.log(fifo_data[i]);
//                     console.log(" ");
//                 }
//                 console.log();
// #endif

                /* If at least 1 set of data, sort the data into U/D/L/R */
                if( bytes_read >= 4 ) {
                    for( i = 0; i < bytes_read; i += 4 ) {
                        gesture_data_.u_data[gesture_data_.index] =
                                                            fifo_data[i + 0];
                        gesture_data_.d_data[gesture_data_.index] =
                                                            fifo_data[i + 1];
                        gesture_data_.l_data[gesture_data_.index] =
                                                            fifo_data[i + 2];
                        gesture_data_.r_data[gesture_data_.index] =
                                                            fifo_data[i + 3];
                        gesture_data_.index++;
                        gesture_data_.total_gestures++;
                    }
                    
// #if DEBUG
//                 console.log("Up Data: ");
//                 for ( i = 0; i < gesture_data_.total_gestures; i++ ) {
//                     console.log(gesture_data_.u_data[i]);
//                     console.log(" ");
//                 }
//                 console.log();
// #endif

                    /* Filter and process gesture data. Decode near/far state */
                    if( processGestureData() ) {
                        if( decodeGesture() ) {
                            //***TODO: U-Turn Gestures
// #if DEBUG
//                             //console.log(gesture_motion_);
// #endif
                        }
                    }
                    
                    /* Reset data */
                    gesture_data_.index = 0;
                    gesture_data_.total_gestures = 0;
                }

            }
        } else {
    
            /* Determine best guessed gesture and clean up */
            delay(FIFO_PAUSE_TIME);
            decodeGesture();
            motion = gesture_motion_;
// #if DEBUG
//             console.log("END: ");
//             console.log(gesture_motion_);
// #endif
            resetGestureParameters();
            return motion;
        }
    }
}

/**
 * Turn the APDS-9960 on
 *
 * @return True if operation successful. False otherwise.
 */
function enablePower()
{
    if( !setMode(POWER, 1) ) {
        return false;
    }
    
    return true;
}

/**
 * Turn the APDS-9960 off
 *
 * @return True if operation successful. False otherwise.
 */
function disablePower()
{
    if( !setMode(POWER, 0) ) {
        return false;
    }
    
    return true;
}

/*******************************************************************************
 * Ambient light and color sensor controls
 ******************************************************************************/

/**
 * @brief Reads the ambient (clear) light level as a 16-bit value
 *
 * @param[out] val value of the light sensor.
 * @return True if operation successful. False otherwise.
 */
function readAmbientLight(val)
{
    var val_byte = [0];
    val = 0;
    
    /* Read value from clear channel, low byte register */
    if( !wireReadDataByte(APDS9960_CDATAL, val_byte) ) {
        return false;
    }
    val = val_byte[0];
    
    /* Read value from clear channel, high byte register */
    if( !wireReadDataByte(APDS9960_CDATAH, val_byte) ) {
        return false;
    }
    val = val + ( val_byte[0] << 8);
    
    return true;
}

/**
 * @brief Reads the red light level as a 16-bit value
 *
 * @param[out] val value of the light sensor.
 * @return True if operation successful. False otherwise.
 */
function readRedLight(val)
{
    var val_byte = [0];
    val = 0;
    
    /* Read value from clear channel, low byte register */
    if( !wireReadDataByte(APDS9960_RDATAL, val_byte) ) {
        return false;
    }
    val = val_byte[0];
    
    /* Read value from clear channel, high byte register */
    if( !wireReadDataByte(APDS9960_RDATAH, val_byte) ) {
        return false;
    }
    val = val + (val_byte[0] << 8);
    
    return true;
}
 
/**
 * @brief Reads the green light level as a 16-bit value
 *
 * @param[out] val value of the light sensor.
 * @return True if operation successful. False otherwise.
 */
function readGreenLight(val)
{
    var val_byte = [0];
    val = 0;
    
    /* Read value from clear channel, low byte register */
    if( !wireReadDataByte(APDS9960_GDATAL, val_byte) ) {
        return false;
    }
    val = val_byte[0];
    
    /* Read value from clear channel, high byte register */
    if( !wireReadDataByte(APDS9960_GDATAH, val_byte) ) {
        return false;
    }
    val = val + (val_byte[0] << 8);
    
    return true;
}

/**
 * @brief Reads the red light level as a 16-bit value
 *
 * @param[out] val value of the light sensor.
 * @return True if operation successful. False otherwise.
 */
function readBlueLight(val)
{
    var val_byte = [0];
    val[0] = 0;
    
    /* Read value from clear channel, low byte register */
    if( !wireReadDataByte(APDS9960_BDATAL, val_byte) ) {
        return false;
    }
    val[0] = val_byte;
    
    /* Read value from clear channel, high byte register */
    if( !wireReadDataByte(APDS9960_BDATAH, val_byte) ) {
        return false;
    }
    val[0] = val[0] + (val_byte[0] << 8);
    
    return true;
}

/*******************************************************************************
 * Proximity sensor controls
 ******************************************************************************/

/**
 * @brief Reads the proximity level as an 8-bit value
 *
 * @param[out] val value of the proximity sensor.
 * @return True if operation successful. False otherwise.
 */
function readProximity( val)
{
    val = [0];
    
    /* Read value from proximity data register */
    if( !wireReadDataByte(PDATA, val) ) {
        return false;
    }
    
    return true;
}

function readProximity2() {
  return i2c.readReg(PDATA);
}


/*******************************************************************************
 * High-level gesture controls
 ******************************************************************************/

/**
 * @brief Resets all the parameters in the gesture data member
 */
function resetGestureParameters()
{
    gesture_data_.index = 0;
    gesture_data_.total_gestures = 0;
    
    gesture_ud_delta_ = 0;
    gesture_lr_delta_ = 0;
    
    gesture_ud_count_ = 0;
    gesture_lr_count_ = 0;
    
    gesture_near_count_ = 0;
    gesture_far_count_ = 0;
    
    gesture_state_ = 0;
    gesture_motion_ = DIR.DIR_NONE;
}

/**
 * @brief Processes the raw gesture data to determine swipe direction
 *
 * @return True if near or far state seen. False otherwise.
 */
function processGestureData()
{
    var u_first = 0;
    var d_first = 0;
    var l_first = 0;
    var r_first = 0;
    var u_last = 0;
    var d_last = 0;
    var l_last = 0;
    var r_last = 0;
    var ud_ratio_first;
    var lr_ratio_first;
    var ud_ratio_last;
    var lr_ratio_last;
    var ud_delta;
    var lr_delta;
    var i;

    /* If we have less than 4 total gestures, that's not enough */
    if( gesture_data_.total_gestures <= 4 ) {
        return false;
    }
    
    /* Check to make sure our data isn't out of bounds */
    if( (gesture_data_.total_gestures <= 32) && 
        (gesture_data_.total_gestures > 0) ) {
        
        /* Find the first value in U/D/L/R above the threshold */
        for( i = 0; i < gesture_data_.total_gestures; i++ ) {
            if( (gesture_data_.u_data[i] > GESTURE_THRESHOLD_OUT) &&
                (gesture_data_.d_data[i] > GESTURE_THRESHOLD_OUT) &&
                (gesture_data_.l_data[i] > GESTURE_THRESHOLD_OUT) &&
                (gesture_data_.r_data[i] > GESTURE_THRESHOLD_OUT) ) {
                
                u_first = gesture_data_.u_data[i];
                d_first = gesture_data_.d_data[i];
                l_first = gesture_data_.l_data[i];
                r_first = gesture_data_.r_data[i];
                break;
            }
        }
        
        /* If one of the _first values is 0, then there is no good data */
        if( (u_first == 0) || (d_first == 0) || 
            (l_first == 0) || (r_first == 0) ) {
            
            return false;
        }
        /* Find the last value in U/D/L/R above the threshold */
        for( i = gesture_data_.total_gestures - 1; i >= 0; i-- ) {
// #if DEBUG
//             console.log(F("Finding last: "));
//             console.log(F("U:"));
//             console.log(gesture_data_.u_data[i]);
//             console.log(F(" D:"));
//             console.log(gesture_data_.d_data[i]);
//             console.log(F(" L:"));
//             console.log(gesture_data_.l_data[i]);
//             console.log(F(" R:"));
//             console.log(gesture_data_.r_data[i]);
// #endif
            if( (gesture_data_.u_data[i] > GESTURE_THRESHOLD_OUT) &&
                (gesture_data_.d_data[i] > GESTURE_THRESHOLD_OUT) &&
                (gesture_data_.l_data[i] > GESTURE_THRESHOLD_OUT) &&
                (gesture_data_.r_data[i] > GESTURE_THRESHOLD_OUT) ) {
                
                u_last = gesture_data_.u_data[i];
                d_last = gesture_data_.d_data[i];
                l_last = gesture_data_.l_data[i];
                r_last = gesture_data_.r_data[i];
                break;
            }
        }
    }
    
    /* Calculate the first vs. last ratio of up/down and left/right */
    ud_ratio_first = ((u_first - d_first) * 100) / (u_first + d_first);
    lr_ratio_first = ((l_first - r_first) * 100) / (l_first + r_first);
    ud_ratio_last = ((u_last - d_last) * 100) / (u_last + d_last);
    lr_ratio_last = ((l_last - r_last) * 100) / (l_last + r_last);
       
// #if DEBUG
//     console.log(F("Last Values: "));
//     console.log(F("U:"));
//     console.log(u_last);
//     console.log(F(" D:"));
//     console.log(d_last);
//     console.log(F(" L:"));
//     console.log(l_last);
//     console.log(F(" R:"));
//     console.log(r_last);

//     console.log(F("Ratios: "));
//     console.log(F("UD Fi: "));
//     console.log(ud_ratio_first);
//     console.log(F(" UD La: "));
//     console.log(ud_ratio_last);
//     console.log(F(" LR Fi: "));
//     console.log(lr_ratio_first);
//     console.log(F(" LR La: "));
//     console.log(lr_ratio_last);
// #endif
       
    /* Determine the difference between the first and last ratios */
    ud_delta = ud_ratio_last - ud_ratio_first;
    lr_delta = lr_ratio_last - lr_ratio_first;
    
// #if DEBUG
//     console.log("Deltas: ");
//     console.log("UD: ");
//     console.log(ud_delta);
//     console.log(" LR: ");
//     console.log(lr_delta);
// #endif

    /* Accumulate the UD and LR delta values */
    gesture_ud_delta_ += ud_delta;
    gesture_lr_delta_ += lr_delta;
    
// #if DEBUG
//     console.log("Accumulations: ");
//     console.log("UD: ");
//     console.log(gesture_ud_delta_);
//     console.log(" LR: ");
//     console.log(gesture_lr_delta_);
// #endif
    
    /* Determine U/D gesture */
    if( gesture_ud_delta_ >= GESTURE_SENSITIVITY_1 ) {
        gesture_ud_count_ = 1;
    } else if( gesture_ud_delta_ <= -GESTURE_SENSITIVITY_1 ) {
        gesture_ud_count_ = -1;
    } else {
        gesture_ud_count_ = 0;
    }
    
    /* Determine L/R gesture */
    if( gesture_lr_delta_ >= GESTURE_SENSITIVITY_1 ) {
        gesture_lr_count_ = 1;
    } else if( gesture_lr_delta_ <= -GESTURE_SENSITIVITY_1 ) {
        gesture_lr_count_ = -1;
    } else {
        gesture_lr_count_ = 0;
    }
    
    /* Determine Near/Far gesture */
    if( (gesture_ud_count_ == 0) && (gesture_lr_count_ == 0) ) {
        if( (abs(ud_delta) < GESTURE_SENSITIVITY_2) && 
            (abs(lr_delta) < GESTURE_SENSITIVITY_2) ) {
            
            if( (ud_delta == 0) && (lr_delta == 0) ) {
                gesture_near_count_++;
            } else if( (ud_delta != 0) || (lr_delta != 0) ) {
                gesture_far_count_++;
            }
            
            if( (gesture_near_count_ >= 10) && (gesture_far_count_ >= 2) ) {
                if( (ud_delta == 0) && (lr_delta == 0) ) {
                    gesture_state_ = STA.NEAR_STATE;
                } else if( (ud_delta != 0) && (lr_delta != 0) ) {
                    gesture_state_ = STA.FAR_STATE;
                }
                return true;
            }
        }
    } else {
        if( (abs(ud_delta) < GESTURE_SENSITIVITY_2) && 
            (abs(lr_delta) < GESTURE_SENSITIVITY_2) ) {
                
            if( (ud_delta == 0) && (lr_delta == 0) ) {
                gesture_near_count_++;
            }
            
            if( gesture_near_count_ >= 10 ) {
                gesture_ud_count_ = 0;
                gesture_lr_count_ = 0;
                gesture_ud_delta_ = 0;
                gesture_lr_delta_ = 0;
            }
        }
    }
    
// #if DEBUG
//     console.log("UD_CT: ");
//     console.log(gesture_ud_count_);
//     console.log(" LR_CT: ");
//     console.log(gesture_lr_count_);
//     console.log(" NEAR_CT: ");
//     console.log(gesture_near_count_);
//     console.log(" FAR_CT: ");
//     console.log(gesture_far_count_);
//     console.log("----------");
// #endif
    
    return false;
}

/**
 * @brief Determines swipe direction or near/far state
 *
 * @return True if near/far event. False otherwise.
 */
function decodeGesture()
{
    /* Return if near or far event is detected */
    if( gesture_state_ == STA.NEAR_STATE ) {
        gesture_motion_ = DIR.DIR_NEAR;
        return true;
    } else if ( gesture_state_ == STA.FAR_STATE ) {
        gesture_motion_ = DIR.DIR_FAR;
        return true;
    }
    
    /* Determine swipe direction */
    if( (gesture_ud_count_ == -1) && (gesture_lr_count_ == 0) ) {
        gesture_motion_ = DIR.DIR_UP;
    } else if( (gesture_ud_count_ == 1) && (gesture_lr_count_ == 0) ) {
        gesture_motion_ = DIR.DIR_DOWN;
    } else if( (gesture_ud_count_ == 0) && (gesture_lr_count_ == 1) ) {
        gesture_motion_ = DIR.DIR_RIGHT;
    } else if( (gesture_ud_count_ == 0) && (gesture_lr_count_ == -1) ) {
        gesture_motion_ = DIR.DIR_LEFT;
    } else if( (gesture_ud_count_ == -1) && (gesture_lr_count_ == 1) ) {
        if( abs(gesture_ud_delta_) > abs(gesture_lr_delta_) ) {
            gesture_motion_ = DIR.DIR_UP;
        } else {
            gesture_motion_ = DIR.DIR_RIGHT;
        }
    } else if( (gesture_ud_count_ == 1) && (gesture_lr_count_ == -1) ) {
        if( abs(gesture_ud_delta_) > abs(gesture_lr_delta_) ) {
            gesture_motion_ = DIR.DIR_DOWN;
        } else {
            gesture_motion_ = DIR.DIR_LEFT;
        }
    } else if( (gesture_ud_count_ == -1) && (gesture_lr_count_ == -1) ) {
        if( abs(gesture_ud_delta_) > abs(gesture_lr_delta_) ) {
            gesture_motion_ = DIR.DIR_UP;
        } else {
            gesture_motion_ = DIR.DIR_LEFT;
        }
    } else if( (gesture_ud_count_ == 1) && (gesture_lr_count_ == 1) ) {
        if( abs(gesture_ud_delta_) > abs(gesture_lr_delta_) ) {
            gesture_motion_ = DIR.DIR_DOWN;
        } else {
            gesture_motion_ = DIR.DIR_RIGHT;
        }
    } else {
        return false;
    }
    
    return true;
}

/*******************************************************************************
 * Getters and setters for register values
 ******************************************************************************/

/**
 * @brief Returns the lower threshold for proximity detection
 *
 * @return lower threshold
 */
function getProxIntLowThresh()
{
    var val = [0];
    
    /* Read value from PILT register */
    if( !wireReadDataByte(APDS9960_PILT, val) ) {
        val[0] = 0;
    }
    
    return val[0];
}

/**
 * @brief Sets the lower threshold for proximity detection
 *
 * @param[in] threshold the lower proximity threshold
 * @return True if operation successful. False otherwise.
 */
function setProxIntLowThresh( threshold)
{
    if( !wireWriteDataByte(APDS9960_PILT, threshold) ) {
        return false;
    }
    
    return true}

/**
 * @brief Returns the high threshold for proximity detection
 *
 * @return high threshold
 */
function getProxIntHighThresh()
{
    var val = [0];
    
    /* Read value from PIHT register */
    if( !wireReadDataByte(APDS9960_PIHT, val) ) {
        val[0] = 0;
    }
    
    return val[0];
}

/**
 * @brief Sets the high threshold for proximity detection
 *
 * @param[in] threshold the high proximity threshold
 * @return True if operation successful. False otherwise.
 */
function setProxIntHighThresh( threshold)
{
    if( !wireWriteDataByte(APDS9960_PIHT, threshold) ) {
        return false;
    }
    
    return true;
}

/**
 * @brief Returns LED drive strength for proximity and ALS
 *
 * Value    LED Current
 *   0        100 mA
 *   1         50 mA
 *   2         25 mA
 *   3         12.5 mA
 *
 * @return the value of the LED drive strength. 0xFF on failure.
 */
function getLEDDrive()
{
    var val = [0];
    
    /* Read value from CONTROL register */
    if( !wireReadDataByte(CONTROL, val) ) {
        return ERROR;
    }
    
    /* Shift and mask out LED drive bits */
    val[0] = (val[0] >> 6) & ((1 << 1) +1);/*0b00000011*/
    
    return val;
}

/**
 * @brief Sets the LED drive strength for proximity and ALS
 *
 * Value    LED Current
 *   0        100 mA
 *   1         50 mA
 *   2         25 mA
 *   3         12.5 mA
 *
 * @param[in] drive the value (0-3) for the LED drive strength
 * @return True if operation successful. False otherwise.
 */
function setLEDDrive( drive)
{
    var val = [0];
    
    /* Read value from CONTROL register */
    if( !wireReadDataByte(CONTROL, val) ) {
        return false;
    }
    
    /* Set bits in register to given value */
    drive &= ((1 << 1) +1);
    drive = drive << 6;
    val[0] &= ((1<<5)+(1<<4)+(1<<3)+(1<<2)+(1<<1)+1);//0b00111111;
    val[0] |= drive;
    
    /* Write register value back into CONTROL register */
    if( !wireWriteDataByte(CONTROL, val) ) {
        return false;
    }
    
    return true;
}

/**
 * @brief Returns receiver gain for proximity detection
 *
 * Value    Gain
 *   0       1x
 *   1       2x
 *   2       4x
 *   3       8x
 *
 * @return the value of the proximity gain. 0xFF on failure.
 */
function getProximityGain()
{
    var val= [0];
    
    /* Read value from CONTROL register */
    if( !wireReadDataByte(CONTROL, val) ) {
        return ERROR;
    }
    
    /* Shift and mask out PDRIVE bits */
    val[0] = (val[0] >> 2) & ((1 << 1) +1)//0b00000011;
    
    return val[0];
}

/**
 * @brief Sets the receiver gain for proximity detection
 *
 * Value    Gain
 *   0       1x
 *   1       2x
 *   2       4x
 *   3       8x
 *
 * @param[in] drive the value (0-3) for the gain
 * @return True if operation successful. False otherwise.
 */
function setProximityGain( drive)
{
    var val = [0];
    
    /* Read value from CONTROL register */
    if( !wireReadDataByte(CONTROL, val) ) {
        return false;
    }
    
    /* Set bits in register to given value */
    drive &= ((1 << 1) +1)//0b00000011;
    drive = drive << 2;
    val[0] &= ((1<<7)+(1<<6)+(1<<5)+(1<<4)+(1<<1)+1)//0b11110011;
    val[0] |= drive;
    
    /* Write register value back into CONTROL register */
    if( !wireWriteDataByte(CONTROL, val) ) {
        return false;
    }
    
    return true;
}

/**
 * @brief Returns receiver gain for the ambient light sensor (ALS)
 *
 * Value    Gain
 *   0        1x
 *   1        4x
 *   2       16x
 *   3       64x
 *
 * @return the value of the ALS gain. 0xFF on failure.
 */
function getAmbientLightGain()
{
    var val = [0];
    
    /* Read value from CONTROL register */
    if( !wireReadDataByte(CONTROL, val) ) {
        return ERROR;
    }
    
    /* Shift and mask out ADRIVE bits */
    val[0] &= ((1<<1)+1);//0b00000011;
    
    return val;
}

/**
 * @brief Sets the receiver gain for the ambient light sensor (ALS)
 *
 * Value    Gain
 *   0        1x
 *   1        4x
 *   2       16x
 *   3       64x
 *
 * @param[in] drive the value (0-3) for the gain
 * @return True if operation successful. False otherwise.
 */
function setAmbientLightGain( drive)
{
    var val = [0];
    
    /* Read value from CONTROL register */
    if( !wireReadDataByte(CONTROL, val) ) {
        return false;
    }
    
    /* Set bits in register to given value */
    drive &= ((1<<1)+1);//0b00000011;
    val[0] &= ((1<<7)+(1<<6)+(1<<5)+(1<<4)+(1<<3)+(1<<2));//0b11111100;
    val[0] |= drive;
    
    /* Write register value back into CONTROL register */
    if( !wireWriteDataByte(CONTROL, val) ) {
        return false;
    }
    
    return true;
}

/**
 * @brief Get the current LED boost value
 * 
 * Value  Boost Current
 *   0        100%
 *   1        150%
 *   2        200%
 *   3        300%
 *
 * @return The LED boost value. 0xFF on failure.
 */
function getLEDBoost()
{
    var val = [0];
    
    /* Read value from CONFIG2 register */
    if( !wireReadDataByte(CONFIG2, val) ) {
        return ERROR;
    }
    
    /* Shift and mask out LED_BOOST bits */
    val[0] = (val[0] >> 4) & ((1<<1)+1);//0b00000011;
    
    return val;
}

/**
 * @brief Sets the LED current boost value
 *
 * Value  Boost Current
 *   0        100%
 *   1        150%
 *   2        200%
 *   3        300%
 *
 * @param[in] drive the value (0-3) for current boost (100-300%)
 * @return True if operation successful. False otherwise.
 */
function setLEDBoost( boost)
{
    var val = [0];
    
    /* Read value from CONFIG2 register */
    if( !wireReadDataByte(CONFIG2, val) ) {
        return false;
    }
    
    /* Set bits in register to given value */
    boost &= ((1<<1)+1);//0b00000011;
    boost = boost << 4;
    val[0] &= ((1<<7)+(1<<6)+(1<<3)+(1<<2)+(1<<1)+1);//0b11001111;
    val[0] |= boost;
    
    /* Write register value back into CONFIG2 register */
    if( !wireWriteDataByte(CONFIG2, val) ) {
        return false;
    }
    
    return true;
}    
   
/**
 * @brief Gets proximity gain compensation enable
 *
 * @return 1 if compensation is enabled. 0 if not. 0xFF on error.
 */
function getProxGainCompEnable()
{
    var val = [0];
    
    /* Read value from CONFIG3 register */
    if( !wireReadDataByte(CONFIG3, val) ) {
        return ERROR;
    }
    
    /* Shift and mask out PCMP bits */
    val[0] = (val[0] >> 5) & 1;//0b00000001;
    
    return val[0];
}

/**
 * @brief Sets the proximity gain compensation enable
 *
 * @param[in] enable 1 to enable compensation. 0 to disable compensation.
 * @return True if operation successful. False otherwise.
 */
 function setProxGainCompEnable( enable)
{
    var val = [0];
    
    /* Read value from CONFIG3 register */
    if( !wireReadDataByte(CONFIG3, val) ) {
        return false;
    }
    
    /* Set bits in register to given value */
    enable &= 1;//0b00000001;
    enable = enable << 5;
    val[0] &= ((1<<7)+(1<<6)+(1<<4)+(1<<3)+(1<<2)+(1<<1)+1);//0b11011111;
    val[0] |= enable;
    
    /* Write register value back into CONFIG3 register */
    if( !wireWriteDataByte(CONFIG3, val) ) {
        return false;
    }
    
    return true;
}

/**
 * @brief Gets the current mask for enabled/disabled proximity photodiodes
 *
 * 1 = disabled, 0 = enabled
 * Bit    Photodiode
 *  3       UP
 *  2       DOWN
 *  1       LEFT
 *  0       RIGHT
 *
 * @return Current proximity mask for photodiodes. 0xFF on error.
 */
function getProxPhotoMask()
{
    var val = [0];
    
    /* Read value from CONFIG3 register */
    if( !wireReadDataByte(CONFIG3, val) ) {
        return ERROR;
    }
    
    /* Mask out photodiode enable mask bits */
    val[0] &= ((1<<3)+(1<<2)+(1<<1)+1);//0b00001111;
    
    return val[0];
}

/**
 * @brief Sets the mask for enabling/disabling proximity photodiodes
 *
 * 1 = disabled, 0 = enabled
 * Bit    Photodiode
 *  3       UP
 *  2       DOWN
 *  1       LEFT
 *  0       RIGHT
 *
 * @param[in] mask 4-bit mask value
 * @return True if operation successful. False otherwise.
 */
function setProxPhotoMask( mask)
{
    var val= [0];
    
    /* Read value from CONFIG3 register */
    if( !wireReadDataByte(CONFIG3, val) ) {
        return false;
    }
    
    /* Set bits in register to given value */
    mask &= ((1<<3)+(1<<2)+(1<<1)+1);//0b00001111;
    val[0] &= ((1<<7)+(1<<6)+(1<<5)+(1<<4));//0b11110000;
    val[0] |= mask;
    
    /* Write register value back into CONFIG3 register */
    if( !wireWriteDataByte(CONFIG3, val) ) {
        return false;
    }
    
    return true;
}

/**
 * @brief Gets the entry proximity threshold for gesture sensing
 *
 * @return Current entry proximity threshold.
 */
function getGestureEnterThresh()
{
    var val = [0];
    
    /* Read value from GPENTH register */
    if( !wireReadDataByte(APDS9960_GPENTH, val) ) {
        val[0] = 0;
    }
    
    return val[0];
}

/**
 * @brief Sets the entry proximity threshold for gesture sensing
 *
 * @param[in] threshold proximity value needed to start gesture mode
 * @return True if operation successful. False otherwise.
 */
function setGestureEnterThresh( threshold)
{
    if( !wireWriteDataByte(APDS9960_GPENTH, threshold) ) {
        return false;
    }
    
    return true;
}

/**
 * @brief Gets the exit proximity threshold for gesture sensing
 *
 * @return Current exit proximity threshold.
 */
function getGestureExitThresh()
{
    var val = [0];
    
    /* Read value from GEXTH register */
    if( !wireReadDataByte(APDS9960_GEXTH, val) ) {
        val[0] = 0;
    }
    
    return val[0];
}

/**
 * @brief Sets the exit proximity threshold for gesture sensing
 *
 * @param[in] threshold proximity value needed to end gesture mode
 * @return True if operation successful. False otherwise.
 */
function setGestureExitThresh( threshold)
{
    if( !wireWriteDataByte(APDS9960_GEXTH, threshold) ) {
        return false;
    }
    
    return true;
}

/**
 * @brief Gets the gain of the photodiode during gesture mode
 *
 * Value    Gain
 *   0       1x
 *   1       2x
 *   2       4x
 *   3       8x
 *
 * @return the current photodiode gain. 0xFF on error.
 */
function getGestureGain()
{
    var val = [0];
    
    /* Read value from GCONF2 register */
    if( !wireReadDataByte(APDS9960_GCONF2, val) ) {
        return ERROR;
    }
    
    /* Shift and mask out GGAIN bits */
    val[0] = (val[0] >> 5) & ((1<<1)+1);//0b00000011;
    
    return val[0];
}

/**
 * @brief Sets the gain of the photodiode during gesture mode
 *
 * Value    Gain
 *   0       1x
 *   1       2x
 *   2       4x
 *   3       8x
 *
 * @param[in] gain the value for the photodiode gain
 * @return True if operation successful. False otherwise.
 */
function setGestureGain( gain)
{
    var val = [0];
    
    /* Read value from GCONF2 register */
    if( !wireReadDataByte(APDS9960_GCONF2, val) ) {
        return false;
    }
    
    /* Set bits in register to given value */
    gain &= ((1<<1)+1);//0b00000011;
    gain = gain << 5;
    val[0] &= ((1<<7)+(1<<4)+(1<<3)+(1<<2)+(1<<1)+1);//0b10011111;
    val[0] |= gain;
    
    /* Write register value back into GCONF2 register */
    if( !wireWriteDataByte(APDS9960_GCONF2, val) ) {
        return false;
    }
    
    return true;
}

/**
 * @brief Gets the drive current of the LED during gesture mode
 *
 * Value    LED Current
 *   0        100 mA
 *   1         50 mA
 *   2         25 mA
 *   3         12.5 mA
 *
 * @return the LED drive current value. 0xFF on error.
 */
function getGestureLEDDrive()
{
    var val = [0];
    
    /* Read value from GCONF2 register */
    if( !wireReadDataByte(APDS9960_GCONF2, val) ) {
        return ERROR;
    }
    
    /* Shift and mask out GLDRIVE bits */
    val[0] = (val[0] >> 3) & ((1<<1)+1);//0b00000011;
    
    return val;
}

/**
 * @brief Sets the LED drive current during gesture mode
 *
 * Value    LED Current
 *   0        100 mA
 *   1         50 mA
 *   2         25 mA
 *   3         12.5 mA
 *
 * @param[in] drive the value for the LED drive current
 * @return True if operation successful. False otherwise.
 */
function setGestureLEDDrive( drive)
{
    var val = [0];
    
    /* Read value from GCONF2 register */
    if( !wireReadDataByte(APDS9960_GCONF2, val) ) {
        return false;
    }
    
    /* Set bits in register to given value */
    drive &= ((1<<1)+1);//0b00000011;
    drive = drive << 3;
    val[0] &= ((1<<7)+(1<<6)+(1<<5)+(1<<2)+(1<<1)+1);//0b11100111;
    val[0] |= drive;
    
    /* Write register value back into GCONF2 register */
    if( !wireWriteDataByte(APDS9960_GCONF2, val) ) {
        return false;
    }
    
    return true;
}

/**
 * @brief Gets the time in low power mode between gesture detections
 *
 * Value    Wait time
 *   0          0 ms
 *   1          2.8 ms
 *   2          5.6 ms
 *   3          8.4 ms
 *   4         14.0 ms
 *   5         22.4 ms
 *   6         30.8 ms
 *   7         39.2 ms
 *
 * @return the current wait time between gestures. 0xFF on error.
 */
function getGestureWaitTime()
{
    var val = [0];
    
    /* Read value from GCONF2 register */
    if( !wireReadDataByte(APDS9960_GCONF2, val) ) {
        return ERROR;
    }
    
    /* Mask out GWTIME bits */
    val[0] &= ((1<<2)+(1<<1)+1);//0b00000111;
    
    return val;
}

/**
 * @brief Sets the time in low power mode between gesture detections
 *
 * Value    Wait time
 *   0          0 ms
 *   1          2.8 ms
 *   2          5.6 ms
 *   3          8.4 ms
 *   4         14.0 ms
 *   5         22.4 ms
 *   6         30.8 ms
 *   7         39.2 ms
 *
 * @param[in] the value for the wait time
 * @return True if operation successful. False otherwise.
 */
function setGestureWaitTime( time)
{
    var val = [0];
    
    /* Read value from GCONF2 register */
    if( !wireReadDataByte(APDS9960_GCONF2, val) ) {
        return false;
    }
    
    /* Set bits in register to given value */
    time &= ((1<<2)+(1<<1)+1);//0b00000111;
    val[0] &= ((1<<7)+(1<<6)+(1<<5)+(1<<4)+(1<<3));//0b11111000;
    val[0] |= time;
    
    /* Write register value back into GCONF2 register */
    if( !wireWriteDataByte(APDS9960_GCONF2, val) ) {
        return false;
    }
    
    return true;
}

/**
 * @brief Gets the low threshold for ambient light interrupts
 *
 * @param[out] threshold current low threshold stored on the APDS-9960
 * @return True if operation successful. False otherwise.
 */
function getLightIntLowThreshold(threshold)
{
    var val_byte = [0];
    threshold = 0;
    
    /* Read value from ambient light low threshold, low byte register */
    if( !wireReadDataByte(APDS9960_AILTL, val_byte) ) {
        return false;
    }
    threshold = val_byte[0];
    
    /* Read value from ambient light low threshold, high byte register */
    if( !wireReadDataByte(APDS9960_AILTH, val_byte) ) {
        return false;
    }
    threshold = threshold + (val_byte[0] << 8);
    
    return true;
}

/**
 * @brief Sets the low threshold for ambient light interrupts
 *
 * @param[in] threshold low threshold value for interrupt to trigger
 * @return True if operation successful. False otherwise.
 */
function setLightIntLowThreshold( threshold)
{
    var val_low = [0];
    var val_high = [0];
    
    /* Break 16-bit threshold into 2 8-bit values */
    val_low[0] = threshold & 0x00FF;
    val_high[0] = (threshold & 0xFF00) >> 8;
    
    /* Write low byte */
    if( !wireWriteDataByte(APDS9960_AILTL, val_low) ) {
        return false;
    }
    
    /* Write high byte */
    if( !wireWriteDataByte(APDS9960_AILTH, val_high) ) {
        return false;
    }
    
    return true;
}

/**
 * @brief Gets the high threshold for ambient light interrupts
 *
 * @param[out] threshold current low threshold stored on the APDS-9960
 * @return True if operation successful. False otherwise.
 */
function getLightIntHighThreshold( threshold)
{
    var val_byte = [0];
    threshold = 0;
    
    /* Read value from ambient light high threshold, low byte register */
    if( !wireReadDataByte(APDS9960_AIHTL, val_byte) ) {
        return false;
    }
    threshold = val_byte[0];
    
    /* Read value from ambient light high threshold, high byte register */
    if( !wireReadDataByte(APDS9960_AIHTH, val_byte) ) {
        return false;
    }
    threshold = threshold + (val_byte[0] << 8);
    
    return true;
}

/**
 * @brief Sets the high threshold for ambient light interrupts
 *
 * @param[in] threshold high threshold value for interrupt to trigger
 * @return True if operation successful. False otherwise.
 */
function setLightIntHighThreshold(threshold)
{
    var val_low =[0];
    var val_high = [0];
    
    /* Break 16-bit threshold into 2 8-bit values */
    val_low[0] = threshold & 0x00FF;
    val_high[0] = (threshold & 0xFF00) >> 8;
    
    /* Write low byte */
    if( !wireWriteDataByte(APDS9960_AIHTL, val_low) ) {
        return false;
    }
    
    /* Write high byte */
    if( !wireWriteDataByte(APDS9960_AIHTH, val_high) ) {
        return false;
    }
    
    return true;
}

/**
 * @brief Gets the low threshold for proximity interrupts
 *
 * @param[out] threshold current low threshold stored on the APDS-9960
 * @return True if operation successful. False otherwise.
 */
function getProximityIntLowThreshold( threshold)
{
    threshold = [0];
    
    /* Read value from proximity low threshold register */
    if( !wireReadDataByte(APDS9960_PILT, threshold) ) {
        return false;
    }
    
    return true;
}

/**
 * @brief Sets the low threshold for proximity interrupts
 *
 * @param[in] threshold low threshold value for interrupt to trigger
 * @return True if operation successful. False otherwise.
 */
function setProximityIntLowThreshold( threshold)
{
    
    /* Write threshold value to register */
    if( !wireWriteDataByte(APDS9960_PILT, threshold) ) {
        return false;
    }
    
    return true;
}
    
/**
 * @brief Gets the high threshold for proximity interrupts
 *
 * @param[out] threshold current low threshold stored on the APDS-9960
 * @return True if operation successful. False otherwise.
 */
function getProximityIntHighThreshold( threshold)
{
    threshold = [0];
    
    /* Read value from proximity low threshold register */
    if( !wireReadDataByte(APDS9960_PIHT, threshold) ) {
        return false;
    }
    
    return true;
}

/**
 * @brief Sets the high threshold for proximity interrupts
 *
 * @param[in] threshold high threshold value for interrupt to trigger
 * @return True if operation successful. False otherwise.
 */
function setProximityIntHighThreshold( threshold)
{
    
    /* Write threshold value to register */
    if( !wireWriteDataByte(APDS9960_PIHT, threshold) ) {
        return false;
    }
    
    return true;
}

/**
 * @brief Gets if ambient light interrupts are enabled or not
 *
 * @return 1 if interrupts are enabled, 0 if not. 0xFF on error.
 */
function getAmbientLightIntEnable()
{
    var val = [0];
    
    /* Read value from ENABLE register */
    if( !wireReadDataByte(ENABLE, val) ) {
        return ERROR;
    }
    
    /* Shift and mask out AIEN bit */
    val[0] = (val[0] >> 4) & 1;//0b00000001;
    
    return val[0];
}

/**
 * @brief Turns ambient light interrupts on or off
 *
 * @param[in] enable 1 to enable interrupts, 0 to turn them off
 * @return True if operation successful. False otherwise.
 */
function setAmbientLightIntEnable( enable)
{
    var val = [0];
    
    /* Read value from ENABLE register */
    if( !wireReadDataByte(ENABLE, val) ) {
        return false;
    }
    
    /* Set bits in register to given value */
    enable &= 1;//0b00000001;
    enable = enable << 4;
    val[0] &= ((1<<7)+(1<<6)+(1<<5)+(1<<3)+(1<<2)+(1<<1)+1);//0b11101111;
    val[0] |= enable;
    
    /* Write register value back into ENABLE register */
    if( !wireWriteDataByte(ENABLE, val) ) {
        return false;
    }
    
    return true;
}

/**
 * @brief Gets if proximity interrupts are enabled or not
 *
 * @return 1 if interrupts are enabled, 0 if not. 0xFF on error.
 */
function getProximityIntEnable()
{
    var val = [0];
    
    /* Read value from ENABLE register */
    if( !wireReadDataByte(ENABLE, val) ) {
        return ERROR;
    }
    
    /* Shift and mask out PIEN bit */
    val[0] = (val[0] >> 5) & 1;//0b00000001;
    
    return val;
}

/**
 * @brief Turns proximity interrupts on or off
 *
 * @param[in] enable 1 to enable interrupts, 0 to turn them off
 * @return True if operation successful. False otherwise.
 */
function setProximityIntEnable( enable)
{
    var val=[0];
    
    /* Read value from ENABLE register */
    if( !wireReadDataByte(ENABLE, val) ) {
        return false;
    }
    
    /* Set bits in register to given value */
    enable &= 1;//0b00000001;
    enable = enable << 5;
    val[0] &= ((1<<7)+(1<<6)+(1<<4)+(1<<3)+(1<<2)+(1<<1)+1);//0b11011111;
    val[0] |= enable;
    
    /* Write register value back into ENABLE register */
    if( !wireWriteDataByte(ENABLE, val) ) {
        return false;
    }
    
    return true;
}

/**
 * @brief Gets if gesture interrupts are enabled or not
 *
 * @return 1 if interrupts are enabled, 0 if not. 0xFF on error.
 */
function getGestureIntEnable()
{
    var val=[0];
    
    /* Read value from GCONF4 register */
    if( !wireReadDataByte(APDS9960_GCONF4, val) ) {
        return ERROR;
    }
    
    /* Shift and mask out GIEN bit */
    val[0] = (val[0] >> 1) & 1;//0b00000001;
    
    return val[0];
}

/**
 * @brief Turns gesture-related interrupts on or off
 *
 * @param[in] enable 1 to enable interrupts, 0 to turn them off
 * @return True if operation successful. False otherwise.
 */
function setGestureIntEnable( enable)
{
    var val=[0];
    
    /* Read value from GCONF4 register */
    if( !wireReadDataByte(APDS9960_GCONF4, val) ) {
        return false;
    }
    
    /* Set bits in register to given value */
    enable &= 1;//0b00000001;
    enable = enable << 1;
    val[0] &= ((1<<7)+(1<<6)+(1<<5)+(1<<4)+(1<<3)+(1<<2)+1);//0b11111101;
    val[0] |= enable;
    
    /* Write register value back into GCONF4 register */
    if( !wireWriteDataByte(APDS9960_GCONF4, val) ) {
        return false;
    }
    
    return true;
}

/**
 * @brief Clears the ambient light interrupt
 *
 * @return True if operation completed successfully. False otherwise.
 */
function clearAmbientLightInt()
{
    var throwaway=[0];
    if( !wireReadDataByte(APDS9960_AICLEAR, throwaway) ) {
        return false;
    }
    
    return true;
}

/**
 * @brief Clears the proximity interrupt
 *
 * @return True if operation completed successfully. False otherwise.
 */
function clearProximityInt()
{
    var throwaway=[0];
    if( !wireReadDataByte(APDS9960_PICLEAR, throwaway) ) {
        return false;
    }
    
    return true;
}

/**
 * @brief Tells if the gesture state machine is currently running
 *
 * @return 1 if gesture state machine is running, 0 if not. 0xFF on error.
 */
function getGestureMode()
{
    var val=[0];
    
    /* Read value from GCONF4 register */
    if( !wireReadDataByte(APDS9960_GCONF4, val) ) {
        return ERROR;
    }
    
    /* Mask out GMODE bit */
    val[0] &= 1;//0b00000001;
    
    return val[0];
}

/**
 * @brief Tells the state machine to either enter or exit gesture state machine
 *
 * @param[in] mode 1 to enter gesture state machine, 0 to exit.
 * @return True if operation successful. False otherwise.
 */
function setGestureMode( mode)
{
    var val=[0];
    
    /* Read value from GCONF4 register */
    if( !wireReadDataByte(APDS9960_GCONF4, val) ) {
        return false;
    }
    
    /* Set bits in register to given value */
    mode &= 1;//0b00000001;
    val[0] &= ((1<<7)+(1<<6)+(1<<5)+(1<<4)+(1<<3)+(1<<2)+(1<<1));//0b11111110;
    val[0] |= mode;
    
    /* Write register value back into GCONF4 register */
    if( !wireWriteDataByte(APDS9960_GCONF4, val) ) {
        return false;
    }
    
    return true;
}






var proximity_data = 0;

  console.log("------------------------------------");
  console.log("SparkFun APDS-9960 - ProximitySensor");
  console.log("------------------------------------");
  
  // Initialize APDS-9960 (configure I2C and initial values)
  if ( init() ) {
    console.log("APDS-9960 initialization complete");
  } else {
    console.log("Something went wrong during APDS-9960 init!");
  }
  
  // Adjust the Proximity sensor gain
  if ( !setProximityGain(PGAIN_2X) ) {
    console.log("Something went wrong trying to set PGAIN");
  }
  
  // Start running the APDS-9960 proximity sensor (no interrupts)
  if ( enableProximitySensor(false) ) {
    console.log("Proximity sensor is now running");
  } else {
    console.log("Something went wrong during sensor init!");
  }

var loopDelay = 250;

setInterval(function(){
  
  // Read the proximity value
  if ( !readProximity(proximity_data) ) {
    console.log("Error reading proximity value");
  } else {
    console.log("Proximity: ");
    console.log(proximity_data);
    var pro = readProximity2();
    console.log(pro);
      
  }
  
},loopDelay);



