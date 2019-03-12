import units.UnitsTools;
import units.qual.*;

class Multiplication {
    void multiply() {
        // kg
        @kg int kg = 5 * UnitsTools.kg;
        @UnitsRep(
                p = 9,
                bu = {@BUC(u = "g", e = 1)})
        // :: error: (assignment.type.incompatible)
        int z = 3 * UnitsTools.m;

        // g
        @g int g = 5 * UnitsTools.g;
        @UnitsRep(bu = {@BUC(u = "g", e = 1)})
        int alsog = g;
        @UnitsRep(
                p = -3,
                bu = {@BUC(u = "g", e = 1)})
        // :: error: (assignment.type.incompatible)
        int notg = g;
        // :: error: (assignment.type.incompatible)
        g = notg;
        g = alsog;

        // m
        @m int m = 5 * UnitsTools.m;
        @UnitsRep(bu = {@BUC(u = "m", e = 1)})
        int alsom = m;
        @UnitsRep(
                p = 9,
                bu = {@BUC(u = "m", e = 1)})
        // :: error: (assignment.type.incompatible)
        int notm = m;
        // :: error: (assignment.type.incompatible)
        m = notm;
        m = alsom;

        // km
        @km int km = 5 * UnitsTools.km;
        @UnitsRep(
                p = 3,
                bu = {@BUC(u = "m", e = 1)})
        int alsokm = km;
        @UnitsRep(
                p = 9,
                bu = {@BUC(u = "m", e = 1)})
        // :: error: (assignment.type.incompatible)
        int notkm = km;
        // :: error: (assignment.type.incompatible)
        km = notkm;
        km = alsokm;

        // mm
        @mm int mm = 5 * UnitsTools.mm;
        @UnitsRep(
                p = -3,
                bu = {@BUC(u = "m", e = 1)})
        int alsomm = mm;
        @UnitsRep(
                p = 9,
                bu = {@BUC(u = "m", e = 1)})
        // :: error: (assignment.type.incompatible)
        int notmm = mm;
        // :: error: (assignment.type.incompatible)
        mm = notmm;
        mm = alsomm;

        // s
        @s int s = 5 * UnitsTools.s;

        // h
        @h int h = 5 * UnitsTools.h;

        // m * m = m2
        @m2 int area = m * m;
        // :: error: (assignment.type.incompatible)
        @km2 int areambad1 = m * m;
        // :: error: (assignment.type.incompatible)
        @mm2 int areambad2 = m * m;

        // km * km = km2
        @km2 int karea = km * km;
        // :: error: (assignment.type.incompatible)
        @m2 int areakmbad1 = km * km;
        // :: error: (assignment.type.incompatible)
        @mm2 int areakmbad2 = km * km;

        // mm * mm = mm2
        @mm2 int marea = mm * mm;
        // :: error: (assignment.type.incompatible)
        @m2 int areammbad1 = mm * mm;
        // :: error: (assignment.type.incompatible)
        @km2 int areammbad2 = mm * mm;

        // s * mPERs = m
        @mPERs int speedm = 10 * UnitsTools.mPERs;
        @m int lengthm = s * speedm;
        lengthm = speedm * s;
        // :: error: (assignment.type.incompatible)
        @km int lengthmbad1 = s * speedm;
        // :: error: (assignment.type.incompatible)
        @mm int lengthmbad2 = s * speedm;

        // s * mPERs2 = mPERs
        @mPERs2 int accelm = 20 * UnitsTools.mPERs2;
        @mPERs int speedm2 = s * accelm;
        speedm2 = accelm * s;
        // :: error: (assignment.type.incompatible)
        @kmPERh int speedm2bad1 = s * accelm;

        // h * kmPERh = km
        @kmPERh int speedkm = 30 * UnitsTools.kmPERh;
        @km int lengthkm = h * speedkm;
        lengthkm = speedkm * h;
        // :: error: (assignment.type.incompatible)
        @m int lengthkmbad1 = h * speedkm;
        // :: error: (assignment.type.incompatible)
        @mm int lengthkmbad2 = h * speedkm;

        // s * s * mPERs2 = m
        @m int distance = s * s * accelm;
        // if we bracket for order of operations, it also works
        distance = s * (s * accelm);
    }
}
