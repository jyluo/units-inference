import units.qual.*;
import units.UnitsTools;

class Arithmetics {

    @m int m = 5 * UnitsTools.m;
    @s int s = 10 * UnitsTools.s;

    public void Main() {
        int mInferred = m + m;
        @m int mInferredUpperBound = mInferred;

        int sInferred = s - s;
        @s int sInferredUpperBound = sInferred;

        int m2 = m * m;
        @m2 int m2UpperBound = m2;

        int mPERs = m / s;
        @mPERs int mPERsUpperBound = mPERs;
    }

    private void BoxedTypes() {
        Integer mInferred = m + m;
        @m Integer mInferredUpperBound = mInferred;

        Integer sInferred = s - s;
        @s Integer sInferredUpperBound = sInferred;

        Integer m2 = m * m;
        @m2 Integer m2UpperBound = m2;

        Integer mPERs = m / s;
        @mPERs Integer mPERsUpperBound = mPERs;
    }
}