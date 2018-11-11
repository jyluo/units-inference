package units.solvers.backend.gje.representation;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import org.checkerframework.javacutil.BugInCF;
import units.representation.UnitsRepresentationUtils;

public class GJEEquationSet {

    // static reference to the singleton instance
    protected static UnitsRepresentationUtils unitsRepUtils;

    private final Map<String, Set<String>> eqSet = new HashMap<>();

    protected GJEEquationSet() {
        unitsRepUtils = UnitsRepresentationUtils.getInstance();
    }

    protected Map<String, Set<String>> getEquationSet() {
        return eqSet;
    }

    protected void addEquation(String key, String equation) {
        if (!(key == "prefixExponent" || unitsRepUtils.baseUnits().contains(key))) {
            throw new BugInCF("Trying to add an equation for unsupported key " + key);
        }

        if (!eqSet.containsKey(key)) {
            eqSet.put(key, new HashSet<>());
        }

        eqSet.get(key).add(equation);
    }

    protected void union(GJEEquationSet otherSet) {
        for (String key : otherSet.eqSet.keySet()) {

            if (!eqSet.containsKey(key)) {
                eqSet.put(key, new HashSet<>());
            }

            for (String equation : otherSet.eqSet.get(key)) {
                eqSet.get(key).add(equation);
            }
        }
    }
}
