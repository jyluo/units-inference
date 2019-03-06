import units.UnitsTools;
import units.qual.*;

class SubtypingTest {

    void inferTop(@UnknownUnits int y) {
        int x = y;
    }

    void inferBot(int y) {
        // :: fixable-error: (assignment.type.incompatible)
        @UnitsBottom int x = y;
    }

    void inferMeterDoubleBound(@m int x) {
        // @m <: y
        int y = UnitsTools.m;
        // y <: @m
        x = y;
    }

    void inferTopTwoVar(@UnknownUnits int x) {
        // @m <: y
        int y = UnitsTools.m;
        // @s <: y
        y = UnitsTools.s;
        // y <: Top
        x = y;
    }

    void flexibleSuper(@UnitsBottom int x) {
        // typically infers dimensionless
        int y = x;
    }

    // typically infers dimensionless
    void flexibleSub(int x) {
        @UnknownUnits int y = x;
    }

    class DirectSubtypeCases {
        @UnknownUnits int top;
        @Dimensionless int dim;
        @m int m;
        @s int s;
        @UnitsBottom int bot;

        void callTop(@UnknownUnits int top) {}

        void callDim(@Dimensionless int dim) {}

        void callM(@m int m) {}

        void callS(@s int s) {}

        void callBot(@UnitsBottom int bot) {}

        void sat() {
            int inferTop = top;
            int inferDim = dim;
            int inferM = m;
            int inferS = s;
            int inferBot = bot;

            callTop(inferTop);
            callTop(inferDim);
            callTop(inferM);
            callTop(inferS);
            callTop(inferBot);

            callDim(inferDim);
            callDim(inferBot);

            callM(inferM);
            callM(inferBot);

            callS(inferS);
            callS(inferBot);

            callBot(inferBot);
        }

        // void unsat() {
        //     int inferTop = top;
        //     int inferDim = dim;
        //     int inferM = m;
        //     int inferS = s;

        //     // callDim(inferTop);
        //     // callDim(inferM);
        //     // callDim(inferS);

        //     // callM(inferTop);
        //     // callM(inferDim);
        //     // callM(inferS);

        //     // callBot(inferTop);
        //     // callBot(inferDim);
        //     // callBot(inferM);
        //     // callBot(inferS);
        // }
    }
}
