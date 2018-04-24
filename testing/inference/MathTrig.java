import units.qual.*;
import units.UnitsTools;

class MathTrig {
    void Trig() {
        // x should be inferred to be rad
        double x = 10;
        // :: fixable-error: (argument.type.incompatible)
        double expected = Math.acos(x / UnitsTools.rad) * Math.expm1(Math.asin(x / UnitsTools.rad)) -
            // :: fixable-error: (argument.type.incompatible)
            Math.exp(Math.atan(x / UnitsTools.rad)) +
            // :: fixable-error: (argument.type.incompatible)
            Math.floor(x) + Math.cosh(x) - 
            Math.sinh(Math.cbrt(x) * UnitsTools.rad);
    }
}
