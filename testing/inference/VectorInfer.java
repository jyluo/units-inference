import units.qual.*;
import units.UnitsTools;

class VectorInfer {
    @m int aInMeters = 10 * UnitsTools.m;
    @m int bInMeters = 20 * UnitsTools.m;

    int a1 = 30;
    int a2 = 40;

    Vector v1 = new Vector(aInMeters, a1);
    Vector v2 = new Vector(bInMeters, a2);

    class Vector {
        double x;
        double y;

        public Vector(int dist, int angle) {
            this.x = dist * Math.cos(angle);
            this.y = dist * Math.sin(angle);
        }
    }
}

