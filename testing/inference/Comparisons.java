import units.qual.*;
import units.UnitsTools;

class Comparisons {
    @m int m = UnitsTools.m;
    @s int s = UnitsTools.s;

    void Compare() {
        int mInferred = 10;
        if( m < mInferred ) {}
        if( mInferred >= m ) {}
        m = m == mInferred ? m : m;
    }
}
