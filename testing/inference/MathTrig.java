import units.UnitsTools;
import units.qual.*;

class MathTrig {

    void Trig() {
        // x should be inferred to be dimensionless
        double x = 10;
        // ac,as,at should be inferred to be radians
        @rad double ac = Math.acos(x);
        @rad double as = Math.asin(x);
        @rad double at = Math.atan(x);

        double ch = Math.cosh(x * UnitsTools.rad);
        double sh = Math.sinh(x * UnitsTools.rad);
        double th = Math.tanh(x * UnitsTools.rad);

        double f = Math.floor(x);
        double rt = Math.cbrt(x);

        double e1 = Math.expm1(x);
        double e = Math.exp(x);
    }
}
