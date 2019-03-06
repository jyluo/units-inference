import org.checkerframework.framework.qual.PolyAll;
import units.UnitsTools;
import units.qual.*;

class Methods {
    @PolyAll int polyAllMethod(@PolyAll int x) {
        return x;
    }

    @PolyUnit int polyUnitMethod(@PolyUnit int x) {
        return x;
    }

    @PolyUnit int polyUnitMethod(@PolyUnit int x, @PolyUnit int y) {
        return x + y;
    }

    @m int meterMethod(@m int x) {
        return x;
    }

    void polyAllMethodTest() {
        // :: fixable-error: (assignment.type.incompatible)
        @m int pam1 = polyAllMethod(5);

        int pam2 = polyAllMethod(5 * UnitsTools.m);
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

    void chainPolyAllMethodTest() {
        // :: fixable-error: (assignment.type.incompatible)
        @m int cpam1 = polyAllMethod(polyAllMethod(5));

        int cpam2 = polyAllMethod(polyAllMethod(5 * UnitsTools.m));
    }

    void chainPolyUnitMethodTest() {
        // :: fixable-error: (assignment.type.incompatible)
        @m int cpum1 = polyUnitMethod(polyUnitMethod(5));

        int cpum2 = polyUnitMethod(polyUnitMethod(5 * UnitsTools.m));
    }
}
