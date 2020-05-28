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
        // :: fixable-error: (assignment.type.incompatible)
        @m int pum1 = polyUnitMethod(5);

        int pum2 = polyUnitMethod(5 * UnitsTools.m);

        // :: fixable-error: (assignment.type.incompatible)
        @m int pum3 = polyUnitMethod(5, 6);
    }

    void normalMethodTest() {
        // :: fixable-error: (argument.type.incompatible)
        int nm1 = meterMethod(5);
    }

    void chainPolyUnitMethodTest() {
        // :: fixable-error: (assignment.type.incompatible)
        @m int cpum1 = polyUnitMethod(polyUnitMethod(5));

        int cpum2 = polyUnitMethod(polyUnitMethod(5 * UnitsTools.m));
    }
}
