import units.qual.rad;
import units.qual.Dimensionless;
import static java.lang.Math.*;

import units.UnitsTools;
import units.qual.*;

@Dimensionless
class StaticFinalConstants {

    @Dimensionless
    static class MyConstants {
        public static final @Dimensionless double X = ((@Dimensionless int) (10));
        public static final @rad Integer Y = ((@rad int) (Integer.MAX_VALUE));

        public static final @rad int HASUNIT = ((@Dimensionless int) (20)) * UnitsTools.rad;

        public MyConstants() {};
    }

    void inferRadians2(@Dimensionless StaticFinalConstants this) {
        // :: fixable-error: (argument.type.incompatible)
        sin(((@rad double) (MyConstants.X)));

        // :: fixable-error: (argument.type.incompatible)
        tan(MyConstants.Y);

        cos(MyConstants.HASUNIT);
    }
}
