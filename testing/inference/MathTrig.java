import units.UnitsTools;
import units.qual.*;

class MathTrig {
    void Trig() {
        // x should be inferred to be dimensionless
        double x = 10;
        // expected should be inferred to be radians
        @Dimensionless double expected = Math.acos(x) / UnitsTools.rad * Math.expm1(Math.asin(x) / UnitsTools.rad) -
            Math.exp(Math.atan(x) / UnitsTools.rad) +
            Math.floor(x) + Math.cosh(x * UnitsTools.rad) - 
            Math.sinh(Math.cbrt(x) * UnitsTools.rad);
    }
}
