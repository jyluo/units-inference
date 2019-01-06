import units.UnitsTools;
import units.qual.*;

import java.util.*;

class WhileLoopIterator {

    List<Integer> list;

    void test() {
        Iterator<Integer> it = list.iterator();

        @ms int i = (int) it.next();

        while (it.hasNext()) {
            @ms int j = (int) it.next();    // here
        }
    }

    // example from JReactPhysics3d
    void test2() {
        // raw iterator fails because we don't generate a slot for the type arg
        // instead, it is assumed that it is parameterized with @Top Object
        Iterator it = list.iterator();

        @ms int i = (int) it.next();

        while (it.hasNext()) {
            @ms int j = (int) it.next();    // here
        }
    }
}
