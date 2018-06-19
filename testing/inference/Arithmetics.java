import units.UnitsTools;
import units.qual.*;

class Arithmetics {
    @m int m = UnitsTools.m;
    @s int s = UnitsTools.s;

    public void Main() {
        @m int mInferred = m + m;

        @s int sInferred = s - s;

        @m2 int m2 = m * m;

        @mPERs int mPERs = m / s;

        @mPERs int mPERsSecond = mPERs % UnitsTools.m;
    }

    private void BoxedTypes() {
        @m Integer mInferred = m + m;

        @s Integer sInferred = s - s;

        @m2 Integer m2 = m * m;

        @mPERs Integer mPERs = m / s;

        @mPERs Integer mPERsSecond = mPERs % UnitsTools.m;
    }
}
