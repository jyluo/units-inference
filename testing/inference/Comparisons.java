import units.qual.*;
import units.UnitsTools;

class Comparisons {
    @m int m = UnitsTools.m;
    @s int s = UnitsTools.s;

    void Compare() {
        int mInferred = 10;

        // :: fixable-error: (comparison.unit.mismatch)
        if( m < mInferred ) {}

        // :: fixable-error: (comparison.unit.mismatch)
        if( mInferred >= m ) {}

        // :: fixable-error: (comparison.unit.mismatch)
        m = m == mInferred ? m : m;
    }
}
