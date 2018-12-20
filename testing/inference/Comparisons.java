import units.UnitsTools;
import units.qual.*;

class Comparisons {
    @m int m = UnitsTools.m;
    @s int s = UnitsTools.s;

    void compare() {
        int mInferred = 10;

        // :: fixable-error: (comparison.unit.mismatch)
        if (m < mInferred) {
        }

        // :: fixable-error: (comparison.unit.mismatch)
        if (mInferred >= m) {
        }

        // :: fixable-error: (comparison.unit.mismatch)
        @m int y = m == mInferred ? m : m;
    }
}
