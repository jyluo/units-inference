import java.util.Comparator;
import java.util.Objects;
import java.util.function.Supplier;
import units.qual.*;

class JavaUtil {
    @m Double mD;
    @s Double sD;

    Comparator<@UnknownUnits Double> dComparator =
            new Comparator<@UnknownUnits Double>() {
                @Override
                @UnitsCompare(fst = 1, snd = 2)
                public int compare(@UnknownUnits Double o1, @UnknownUnits Double o2) {
                    return o1.compareTo(o2);
                }
            };

    Supplier<String> stringSupplier;

    void testComparator() {
        int x = dComparator.compare(mD, mD);
        // :: error: (comparison.unit.mismatch)
        x = dComparator.compare(mD, sD);
    }

    void testObjects() {
        Objects.equals(mD, mD);
        // :: error: (comparison.unit.mismatch)
        Objects.equals(mD, sD);

        Objects.deepEquals(mD, mD);
        // :: error: (comparison.unit.mismatch)
        Objects.deepEquals(mD, sD);

        Objects.compare(mD, mD, dComparator);
        // :: error: (comparison.unit.mismatch)
        Objects.compare(mD, sD, dComparator);

        Objects.hashCode(mD);
        Objects.hash(mD, sD);
        Objects.toString(mD);
        Objects.toString(mD, "stuff");

        mD = Objects.requireNonNull(mD);
        // :: error: (assignment.type.incompatible)
        mD = Objects.requireNonNull(sD);

        mD = Objects.requireNonNull(mD, "stuff");
        // :: error: (assignment.type.incompatible)
        mD = Objects.requireNonNull(sD, "stuff");

        mD = Objects.requireNonNull(mD, stringSupplier);
        // :: error: (assignment.type.incompatible)
        mD = Objects.requireNonNull(sD, stringSupplier);

        Objects.isNull(mD);
        Objects.nonNull(mD);
    }
}
