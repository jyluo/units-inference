import units.UnitsTools;
import units.qual.*;

class SubtypingTest {

    void inferTop(@UnknownUnits int y) {
        int x = y;
    }

    void inferBot(int y) {
        // :: fixable-error: (assignment.type.incompatible)
        @UnitsBottom int x = y;
    }

    void inferMeterDoubleBound(@m int x) {
        // @m <: y
        int y = UnitsTools.m;
        // y <: @m
        x = y;
    }

    void inferTopTwoVar(@UnknownUnits int x) {
        // @m <: y
        int y = UnitsTools.m;
        // @s <: y
        y = UnitsTools.s;
        // y <: Top
        x = y;
    }

    void flexibleSuper(@UnitsBottom int x) {
        // typically infers dimensionless
        int y = x;
    }

    // typically infers dimensionless
    void flexibleSub(int x) {
        @UnknownUnits int y = x;
    }
}
