import units.UnitsTools;
import units.qual.*;

// import java.lang.reflect.Field;

class ByteCode {

    void test() {
        // StringBuilder(int capacity) is not annotated in the library, so
        // by default it should only pass with dimensionless inputs
        StringBuilder sb = new StringBuilder(5);

        @Dimensionless int sb1Cap = sb.capacity();

        // this only passes with bytecode defaults set to accept top params
        StringBuilder sb2 = new StringBuilder(UnitsTools.s);

        // this only passes with bytecode defaults set to return bottom
        @m int sb2Cap = sb2.capacity();
    }

    void test2() {
        Object theUnsafe = null;
        // try {
        //     Class<?> uc = Class.forName("sun.misc.Unsafe");
        //     Field f = uc.getDeclaredField("theUnsafe");
        //     f.setAccessible(true);
        //     theUnsafe = f.get(uc);
        // } catch (Exception e) {
        // }
        long ptr = 30;
        sun.misc.Unsafe UNSAFE = (sun.misc.Unsafe) theUnsafe;
        UNSAFE.putByte(ptr + UnitsTools.rad, (byte) 20);    // a case in JLargeArrays
    }
}
