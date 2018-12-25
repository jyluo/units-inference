import units.UnitsTools;
import units.qual.*;

class VectorInfer {
    @m int aInMeters = 10 * UnitsTools.m;
    @m int bInMeters = 20 * UnitsTools.m;

    int a1 = 30;
    int a2 = 40;

    // :: fixable-error: (argument.type.incompatible)
    Vector v1 = new Vector(aInMeters, a1);
    // :: fixable-error: (argument.type.incompatible)
    Vector v2 = new Vector(bInMeters, a2);

    class Vector {
        double x;
        double y;

        public Vector(int dist, int angle) {
            // :: fixable-error: (argument.type.incompatible)
            this.x = dist * Math.cos(angle);
            // :: fixable-error: (argument.type.incompatible)
            this.y = dist * Math.sin(angle);
        }
    }
}
