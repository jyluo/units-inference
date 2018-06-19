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

    void doublebound(@m int x) {
        // @m <: y
        int y = UnitsTools.m;
        // y <: @m
        x = y;
    }

    void inferTopTwo(@UnknownUnits int x) {
        // @m <: y
        int y = UnitsTools.m;
        // @s <: y
        y = UnitsTools.s;
        // y <: Top
        x = y;
    }

    void flexibleSuper(@UnitsBottom int x) {
        int y = x;
    }

    void flexibleSub(int x) {
        @UnknownUnits int y = x;
    }
}
