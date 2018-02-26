import units.qual.*;
import units.UnitsTools;

class UnitsToolsConstants {

    public void Main() {
        @UnknownUnits Integer top = 10;

        // :: fixable-error: (assignment.type.incompatible)
        Integer uu = UnitsTools.m;
        // :: fixable-error: (assignment.type.incompatible)
        uu = units.UnitsTools.s;
        // :: fixable-error: (assignment.type.incompatible)
        uu = UnitsTools.ms;
        // :: fixable-error: (assignment.type.incompatible)
        uu = top;

        // :: fixable-error: (assignment.type.incompatible)
        Integer m = UnitsTools.m;

        // :: fixable-error: (assignment.type.incompatible)
        Integer s = UnitsTools.s;

        // :: fixable-error: (assignment.type.incompatible)
        Integer ms = UnitsTools.ms;
    }
}
