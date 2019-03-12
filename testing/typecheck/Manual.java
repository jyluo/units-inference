import units.UnitsTools;
import units.qual.*;

// Include all the examples from the manual here,
// to ensure they work as expected.
class Manual {
    void demo() {
        @m int meters = 5 * UnitsTools.m;
        @s int secs = 2 * UnitsTools.s;
        @mPERs int speed = meters / secs;
        speed = calcSpeed(meters, secs);

        @km int kilometers = 10 * UnitsTools.km;
        // :: error: (argument.type.incompatible)
        speed = calcSpeed(kilometers, secs);
    }

    @mPERs int calcSpeed(@m int d, @s int t) {
        return d / t;
    }
}
