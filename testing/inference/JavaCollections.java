import units.qual.*;
import units.UnitsTools;
import java.util.*;

class JavaCollections {
    void m() {
        List<Integer> x = new ArrayList<>();

        List<@m Integer> y = new ArrayList<>();

        @m Integer meterOne = new @m Integer(5 * UnitsTools.m);
        
        // :: fixable-error: (constructor.invocation.invalid)
        @m Integer meterTwo = new @m Integer(5);

        // :: fixable-error: (argument.type.incompatible)
        x.add(meterTwo);
    }
}
