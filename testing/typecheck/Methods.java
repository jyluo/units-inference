import units.UnitsTools;
import units.qual.*;

class Methods {
    @PolyUnit int polyUnitMethod(@PolyUnit int x) {
        return x;
    }

    @PolyUnit int polyUnitMethod(@PolyUnit int x, @PolyUnit int y) {
        return x + y;
    }

    @m int meterMethod(@m int x) {
        return x;
    }

    void polyUnitMethodTest() {
        // :: error: (assignment.type.incompatible)
        @m int pum1 = polyUnitMethod(5);

        int pum2 = polyUnitMethod(5 * UnitsTools.m);

        // :: error: (assignment.type.incompatible)
        @m int pum3 = polyUnitMethod(5, 6);

        @m int pum4 = polyUnitMethod(UnitsTools.m, UnitsTools.m);

        // :: error: (assignment.type.incompatible)
        @m int pum5 = polyUnitMethod(UnitsTools.m, UnitsTools.s);
    }

    void normalMethodTest() {
        // :: error: (argument.type.incompatible)
        int nm1 = meterMethod(5);
    }

    void chainPolyUnitMethodTest() {
        // :: error: (assignment.type.incompatible)
        @m int cpum1 = polyUnitMethod(polyUnitMethod(5));

        int cpum2 = polyUnitMethod(polyUnitMethod(5 * UnitsTools.m));
    }
}
