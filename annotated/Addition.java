import units.qual.m;
import units.qual.Dimensionless;
import units.qual.UnknownUnits;
import units.qual.s;
import units.qual.UnitsBottom;
import units.UnitsTools;
import units.qual.*;

@Dimensionless
class Addition {
    @m int m = UnitsTools.m;
    @s int s = UnitsTools.s;
    @UnknownUnits int top;
    @UnitsBottom int bot;

    void tops(@Dimensionless Addition this) {
        @UnknownUnits
        int a = top + top;
        @UnknownUnits
        int b = top + bot;
        @UnknownUnits
        int c = bot + top;
        @UnknownUnits
        int d = top + m;
        @UnknownUnits
        int e = s + top;

        // unsat cases:
        // @m int ua = top + top;
        // @m int ub = top + bot;
        // @m int uc = bot + top;
        // @m int ud = top + m;
        // @m int ue = s + top;
    }

    void bots(@Dimensionless Addition this) {
        @UnitsBottom
        int a = bot + bot;
        @m
        int b = bot + m;
        @s
        int c = s + bot;
    }

    void units(@Dimensionless Addition this) {
        @m
        int a = m + m;
        @UnknownUnits
        double b = Math.PI + m;

        // unsat cases:
        // @s int ua = m + m;
        // @s double ub = Math.PI + m;
    }

    void slots(@Dimensionless Addition this) {
        @m
        int a = m + m;
        @m
        int b = m + a;
        @m
        int c = a + m;
        @m
        int d = b + b;
        @m
        int e = b + c;
    }
}
