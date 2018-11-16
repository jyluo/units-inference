import units.UnitsTools;
import units.qual.*;

class OverSpecified {
    void over(@m int m, @s int s) {
        int x = m;

        int y = s;

        y = UnitsTools.s;

        y = UnitsTools.s;
    }
}
