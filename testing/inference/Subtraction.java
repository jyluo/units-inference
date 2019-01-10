import units.UnitsTools;
import units.qual.*;

class Subtraction {
    @m int m = UnitsTools.m;
    @s int s = UnitsTools.s;
    @UnknownUnits int top;
    @UnitsBottom int bot;

    void tops() {
        int a = top - top;
        int b = top - bot;
        int c = bot - top;
        int d = top - m;
        int e = s - top;

        // unsat cases:
        // @m int ua = top - top;
        // @m int ub = top - bot;
        // @m int uc = bot - top;
        // @m int ud = top - m;
        // @m int ue = s - top;
    }

    void bots() {
        int a = bot - bot;
        int b = bot - m;
        int c = s - bot;
    }

    void units() {
        @m int a = m - m;
        @UnknownUnits double b = Math.PI - m;

        // unsat cases:
        // @s int ua = m - m;
        // @s double ub = Math.PI - m;
    }

    void slots() {
        int a = m - m;
        int b = m - a;
        int c = a - m;
        int d = b - b;
        int e = b - c;
    }
}
