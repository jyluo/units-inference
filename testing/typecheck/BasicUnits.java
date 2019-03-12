import units.UnitsTools;
import units.qual.*;

class BasicUnits {
    void demo() {
        // :: error: (assignment.type.incompatible)
        @m int merr = 5;

        @m int m = 5 * UnitsTools.m;
        @s int s = 9 * UnitsTools.s;

        // :: error: (assignment.type.incompatible)
        @km int kmerr = 10;
        @km int km = 10 * UnitsTools.km;

        // this is allowed, unqualified is a supertype of all units
        int bad = m / s;

        @mPERs int good = m / s;

        // :: error: (assignment.type.incompatible)
        @mPERs int b1 = s / m;

        // :: error: (assignment.type.incompatible)
        @mPERs int b2 = m * s;

        @mPERs2 int goodaccel = m / s / s;

        // :: error: (assignment.type.incompatible)
        @mPERs2 int badaccel1 = s / m / s;

        // :: error: (assignment.type.incompatible)
        @mPERs2 int badaccel2 = s / s / m;

        // :: error: (assignment.type.incompatible)
        @mPERs2 int badaccel3 = s * s / m;

        // :: error: (assignment.type.incompatible)
        @mPERs2 int badaccel4 = m * s * s;

        @m2 int area = m * m;

        // :: error: (assignment.type.incompatible)
        @km2 int bae1 = m * m;

        @rad double rad = 20.0d * UnitsTools.rad;
        @deg double deg = 30.0d * UnitsTools.deg;

        // speed conversion
        @mPERs int mPs = 30 * UnitsTools.mPERs;
        @kmPERh int kmPhr = 20 * UnitsTools.kmPERh;

        // speeds
        @km int kilometers = 10 * UnitsTools.km;
        @h int hours = UnitsTools.h;
        @kmPERh int speed = kilometers / hours;

        // Addition/substraction only accepts another @kmPERh value
        // :: error: (assignment.type.incompatible)
        speed = speed + 5;
        // :: error: (compound.assignment.type.incompatible)
        speed += 5;

        speed += speed;
        speed = (speed += speed);

        // Multiplication/division with an unqualified type is allowed
        speed = kilometers / hours * 2;
        speed /= 2;

        speed = (speed /= 2);
    }

    void unitsRepTest() {
        @m int x = 5 * UnitsTools.m;
        @UnitsRep(
                p = 3,
                bu = {@BUC(u = "m", e = 1)})
        int y = 2 * UnitsTools.km;
        @UnitsRep(bu = {@BUC(u = "m", e = 1)})
        int z = 3 * UnitsTools.m;
        @km int y2 = 3 * UnitsTools.km;

        // :: error: (assignment.type.incompatible)
        y2 = z;
        // :: error: (assignment.type.incompatible)
        y2 = x;
        // :: error: (assignment.type.incompatible)
        y = z;
        // :: error: (assignment.type.incompatible)
        y = x;

        // :: error: (assignment.type.incompatible)
        y2 = x * x;
        // :: error: (assignment.type.incompatible)
        y2 = z * z;
    }
}
