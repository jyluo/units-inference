import units.UnitsTools;
import units.qual.*;

class Speeds {

    @mPERs int calcSpeed(@m int d, @s int t) {
        return d / t;
    }

    void test() {
        @km int xInKilometers = 10 * UnitsTools.km;
        @m int yInMeters = 20 * UnitsTools.m;

        @s int jInSeconds = 30 * UnitsTools.s;
        @s int kInSeconds = 30 * UnitsTools.s;

        @mPERs int res;

        // :: error: (argument.type.incompatible)
        res = calcSpeed(xInKilometers, jInSeconds); // error!

        res = calcSpeed(yInMeters, kInSeconds); // okay
    }
}
