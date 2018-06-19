import units.UnitsTools;
import units.qual.Dimensionless;
import units.qual.UnknownUnits;
import units.qual.m;
// @skip-test
// need to be able to set default array component qualifier, and fix some crazy bug

@UnknownUnits
class Arrays {
    Arrays() {
        @m int[] arrayOfMeters1 = null;

        @m int[] arrayOfMeters2 = new int @Dimensionless [5];

        @m int[] arrayOfMeters3 = new @m int @Dimensionless [5];

        @m int[] arrayOfMeters4 = new int @Dimensionless [] {UnitsTools.m, UnitsTools.m};

        @m int[] arrayOfMeters5 = new @m int @Dimensionless [] {UnitsTools.m, UnitsTools.m};

        //         @m int[] arrayOfMeters6 = {UnitsTools.m, UnitsTools.m};
    }
}
