import units.UnitsTools;
import units.qual.*;

class Addition {
    // Addition is legal when the operands have the same units.
    void good() {
        // Units
        // Amperes
        @A int aAmpere = 5 * UnitsTools.A;
        @A int bAmpere = 5 * UnitsTools.A;
        @A int sAmpere = aAmpere + bAmpere;

        // Candela
        @cd int aCandela = 5 * UnitsTools.cd;
        @cd int bCandela = 5 * UnitsTools.cd;
        @cd int sCandela = aCandela + bCandela;

        // Celsius
        @C int aCelsius = 5 * UnitsTools.C;
        @C int bCelsius = 5 * UnitsTools.C;
        @C int sCelsius = aCelsius + bCelsius;

        // Gram
        @g int aGram = 5 * UnitsTools.g;
        @g int bGram = 5 * UnitsTools.g;
        @g int sGram = aGram + bGram;

        // Hour
        @h int aHour = 5 * UnitsTools.h;
        @h int bHour = 5 * UnitsTools.h;
        @h int sHour = aHour + bHour;

        // Kelvin
        @K int aKelvin = 5 * UnitsTools.K;
        @K int bKelvin = 5 * UnitsTools.K;
        @K int sKelvin = aKelvin + bKelvin;

        // Kilogram
        @kg int aKilogram = 5 * UnitsTools.kg;
        @kg int bKilogram = 5 * UnitsTools.kg;
        @kg int sKilogram = aKilogram + bKilogram;

        // Kilometer
        @km int aKilometer = 5 * UnitsTools.km;
        @km int bKilometer = 5 * UnitsTools.km;
        @km int sKilometer = aKilometer + bKilometer;

        // Square kilometer
        @km2 int aSquareKilometer = 5 * UnitsTools.km2;
        @km2 int bSquareKilometer = 5 * UnitsTools.km2;
        @km2 int sSquareKilometer = aSquareKilometer + bSquareKilometer;

        // Kilometer per hour
        @kmPERh int aKilometerPerHour = 5 * UnitsTools.kmPERh;
        @kmPERh int bKilometerPerHour = 5 * UnitsTools.kmPERh;
        @kmPERh int sKilometerPerHour = aKilometerPerHour + bKilometerPerHour;

        // Meter
        @m int aMeter = 5 * UnitsTools.m;
        @m int bMeter = 5 * UnitsTools.m;
        @m int sMeter = aMeter + bMeter;

        // Square meter
        @m2 int aSquareMeter = 5 * UnitsTools.m2;
        @m2 int bSquareMeter = 5 * UnitsTools.m2;
        @m2 int sSquareMeter = aSquareMeter + bSquareMeter;

        // Meter per second
        @mPERs int aMeterPerSecond = 5 * UnitsTools.mPERs;
        @mPERs int bMeterPerSecond = 5 * UnitsTools.mPERs;
        @mPERs int sMeterPerSecond = aMeterPerSecond + bMeterPerSecond;

        // Meter per second square
        @mPERs2 int aMeterPerSecondSquare = 5 * UnitsTools.mPERs2;
        @mPERs2 int bMeterPerSecondSquare = 5 * UnitsTools.mPERs2;
        @mPERs2 int sMeterPerSecondSquare = aMeterPerSecondSquare + bMeterPerSecondSquare;

        // Minute
        @min int aMinute = 5 * UnitsTools.min;
        @min int bMinute = 5 * UnitsTools.min;
        @min int sMinute = aMinute + bMinute;

        // Millimeter
        @mm int aMillimeter = 5 * UnitsTools.mm;
        @mm int bMillimeter = 5 * UnitsTools.mm;
        @mm int sMillimeter = aMillimeter + bMillimeter;

        // Square millimeter
        @mm2 int aSquareMillimeter = 5 * UnitsTools.mm2;
        @mm2 int bSquareMillimeter = 5 * UnitsTools.mm2;
        @mm2 int sSquareMillimeter = aSquareMillimeter + bSquareMillimeter;

        // Mole
        @mol int aMole = 5 * UnitsTools.mol;
        @mol int bMole = 5 * UnitsTools.mol;
        @mol int sMole = aMole + bMole;

        // Second
        @s int aSecond = 5 * UnitsTools.s;
        @s int bSecond = 5 * UnitsTools.s;
        @s int sSecond = aSecond + bSecond;
    }

    // Addition is illegal when the operands have different units or one
    // is unqualified. In these tests, we cycle between the result and
    // the first or second operand having an incorrect type.
    void bad() {
        // Units
        // Amperes
        @A int aAmpere = 5 * UnitsTools.A;
        @A int bAmpere = 5 * UnitsTools.A;

        // Candela
        @cd int aCandela = 5 * UnitsTools.cd;
        @cd int bCandela = 5 * UnitsTools.cd;

        // Celsius
        @C int aCelsius = 5 * UnitsTools.C;
        @C int bCelsius = 5 * UnitsTools.C;

        // Gram
        @g int aGram = 5 * UnitsTools.g;
        @g int bGram = 5 * UnitsTools.g;

        // Hour
        @h int aHour = 5 * UnitsTools.h;
        @h int bHour = 5 * UnitsTools.h;

        // Kelvin
        @K int aKelvin = 5 * UnitsTools.K;
        @K int bKelvin = 5 * UnitsTools.K;

        // Kilogram
        @kg int aKilogram = 5 * UnitsTools.kg;
        @kg int bKilogram = 5 * UnitsTools.kg;

        // Kilometer
        @km int aKilometer = 5 * UnitsTools.km;
        @km int bKilometer = 5 * UnitsTools.km;

        // Square kilometer
        @km2 int aSquareKilometer = 5 * UnitsTools.km2;
        @km2 int bSquareKilometer = 5 * UnitsTools.km2;

        // Kilometer per hour
        @kmPERh int aKilometerPerHour = 5 * UnitsTools.kmPERh;
        @kmPERh int bKilometerPerHour = 5 * UnitsTools.kmPERh;

        // Meter
        @m int aMeter = 5 * UnitsTools.m;
        @m int bMeter = 5 * UnitsTools.m;

        // Square meter
        @m2 int aSquareMeter = 5 * UnitsTools.m2;
        @m2 int bSquareMeter = 5 * UnitsTools.m2;

        // Meter per second
        @mPERs int aMeterPerSecond = 5 * UnitsTools.mPERs;
        @mPERs int bMeterPerSecond = 5 * UnitsTools.mPERs;

        // Meter per second square
        @mPERs2 int aMeterPerSecondSquare = 5 * UnitsTools.mPERs2;
        @mPERs2 int bMeterPerSecondSquare = 5 * UnitsTools.mPERs2;

        // Minute
        @min int aMinute = 5 * UnitsTools.min;
        @min int bMinute = 5 * UnitsTools.min;

        // Millimeter
        @mm int aMillimeter = 5 * UnitsTools.mm;
        @mm int bMillimeter = 5 * UnitsTools.mm;

        // Square millimeter
        @mm2 int aSquareMillimeter = 5 * UnitsTools.mm2;
        @mm2 int bSquareMillimeter = 5 * UnitsTools.mm2;

        // Mole
        @mol int aMole = 5 * UnitsTools.mol;
        @mol int bMole = 5 * UnitsTools.mol;

        // Second
        @s int aSecond = 5 * UnitsTools.s;
        @s int bSecond = 5 * UnitsTools.s;

        // Units
        // Amperes
        // :: error: (assignment.type.incompatible)
        @g int sGram = aAmpere + bAmpere;

        // Candela
        // :: error: (assignment.type.incompatible)
        @cd int sCandela = aAmpere + bCandela;

        // Celsius
        // :: error: (assignment.type.incompatible)
        @C int sCelsius = aCelsius + bMillimeter;

        // Gram
        // :: error: (assignment.type.incompatible)
        @kg int sKilogram = aGram + bGram;

        // Hour
        // :: error: (assignment.type.incompatible)
        @h int sHour = aSquareMeter + bHour;

        // Kelvin
        // :: error: (assignment.type.incompatible)
        @K int sKelvin = aKelvin + bSecond;

        // Kilogram
        // :: error: (assignment.type.incompatible)
        @kmPERh int sKilometerPerHour = aKilogram + bKilogram;

        // Kilometer
        // :: error: (assignment.type.incompatible)
        @km int sKilometer = aCandela + bKilometer;

        // Square kilometer
        // :: error: (assignment.type.incompatible)
        @km2 int sSquareKilometer = aSquareKilometer + bAmpere;

        // Kilometer per hour
        // :: error: (assignment.type.incompatible)
        @mPERs int sMeterPerSecond = aKilometerPerHour + bKilometerPerHour;

        // Meter
        // :: error: (assignment.type.incompatible)
        @m int sMeter = aHour + bMeter;

        // Square meter
        // :: error: (assignment.type.incompatible)
        @m2 int sSquareMeter = aSquareMeter + bGram;

        // Meter per second
        // :: error: (assignment.type.incompatible)
        @mm2 int sSquareMillimeter = aMeterPerSecond + bMeterPerSecond;

        // Meter per second square
        // :: error: (assignment.type.incompatible)
        @mPERs2 int sMeterPerSecondSquare = aMeterPerSecondSquare + bMeter;

        // Minute
        // :: error: (assignment.type.incompatible)
        @min int sMinute = aMole + bMinute;

        // Millimeter
        // :: error: (assignment.type.incompatible)
        @mm int sMillimeter = aMillimeter + bHour;

        // Square millimeter
        // :: error: (assignment.type.incompatible)
        @A int sAmpere = aSquareMillimeter + bSquareMillimeter;

        // Mole
        // :: error: (assignment.type.incompatible)
        @mol int sMole = aCandela + bMole;

        // Second
        // :: error: (assignment.type.incompatible)
        @s int sSecond = aSecond + bSquareKilometer;
    }
}
