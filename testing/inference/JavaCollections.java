import java.util.*;
import units.UnitsTools;
import units.qual.*;

class JavaCollections {
    void m() {
        // infers that the list has to be a list of meters
        List<Integer> x = new ArrayList<>();

        List<@m Integer> y = new ArrayList<>();

        @m Integer meterOne = new @m Integer(5 * UnitsTools.m);

        // :: fixable-error: (constructor.invocation.invalid)
        @m Integer meterTwo = new @m Integer(5);

        // :: fixable-error: (argument.type.incompatible)
        x.add(meterTwo);

        Integer meterOut = x.iterator().next();

        // :: fixable-error: (assignment.type.incompatible)
        @m Integer meterOutUpperBound = meterOut;
    }
}
