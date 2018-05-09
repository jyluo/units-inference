import units.qual.*;
import units.UnitsTools;

class Unsat {
    // this method is deliberately unsat

    void test() {
        int m = UnitsTools.m;

        forceBottom(m, m);
    }

    void forceBottom(int m, @UnitsBottom int bot) {}
}