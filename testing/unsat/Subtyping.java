import units.qual.*;

class SubtypingTest {

    void inferTop(@UnknownUnits int y) {
        int z = y;
        @UnitsBottom int x = z;
    }
}
