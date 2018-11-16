import units.UnitsTools;
import units.qual.*;

class UnderConstrained {
    void basic(int z) {
        int x = z;
        int y = x;
    }

    void arithmetics() {
        @m int a = 5 + 6;

        @s int s = 5 - 6;

        int m = 5 * 6;

        int d = 5 / 6;

        int mo = 5 % 6;
    }
}
