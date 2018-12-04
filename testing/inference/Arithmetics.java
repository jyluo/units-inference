import units.UnitsTools;
import units.qual.*;

class Arithmetics {
    @m int m = UnitsTools.m;
    @s int s = UnitsTools.s;

    void primitiveTypes() {
        int mInferred = m + m;

        int sInferred = s - s;

        int m2 = m * m;

        int mPERs = m / s;

        int mPERsSecond = mPERs % UnitsTools.m;
    }

    void boxedTypes() {
        Integer mInferred = m + m;

        Integer sInferred = s - s;

        Integer m2 = m * m;

        Integer mPERs = m / s;

        Integer mPERsSecond = mPERs % UnitsTools.m;
    }

    void twoVariableEquations() {
        int mInferred = 5 + m;

        int sInferred = 5 - s;

        // :: fixable-error: (assignment.type.incompatible)
        @m2 int m2 = 10 * m;

        // :: fixable-error: (assignment.type.incompatible)
        @mPERs int mPERs = m / 20;

        // :: fixable-error: (assignment.type.incompatible)
        @mPERs int mPERsSecond = 20 % UnitsTools.m;
    }

    void threeVariableEquations() {
        int a = 5 + 6;

        int s = 5 - 6;

        int m = 5 * 6;

        int d = 5 / 6;

        int mo = 5 % 6;
    }
}
