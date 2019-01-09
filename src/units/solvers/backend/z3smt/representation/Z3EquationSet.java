package units.solvers.backend.z3smt.representation;

import com.microsoft.z3.BoolExpr;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import org.checkerframework.dataflow.util.HashCodeUtils;
import org.checkerframework.javacutil.BugInCF;
import units.representation.UnitsRepresentationUtils;

public class Z3EquationSet {

    public static final String prefixExponentKey = "prefixExponent";

    // Map<Dimension, Set<BoolExpr>>
    private final Map<String, Set<BoolExpr>> eqSet = new HashMap<>();

    public Z3EquationSet() {}

    public Map<String, Set<BoolExpr>> getEquationSet() {
        return eqSet;
    }

    Set<BoolExpr> getZ3Constraints(String key) {
        return eqSet.get(key);
    }

    public boolean isEmpty() {
        return eqSet.isEmpty();
    }

    public void addEquation(String key, BoolExpr equation) {
        if (!(key == prefixExponentKey
                || UnitsRepresentationUtils.getInstance().baseUnits().contains(key))) {
            throw new BugInCF("Trying to add an equation for unsupported key " + key);
        }

        if (!eqSet.containsKey(key)) {
            eqSet.put(key, new HashSet<>());
        }

        eqSet.get(key).add(equation);
    }

    public void union(Z3EquationSet otherSet) {
        for (Entry<String, Set<BoolExpr>> otherEntry : otherSet.eqSet.entrySet()) {
            String key = otherEntry.getKey();
            if (!eqSet.containsKey(key)) {
                eqSet.put(key, new HashSet<>());
            }
            Set<BoolExpr> myEquations = eqSet.get(key);
            for (BoolExpr equation : otherEntry.getValue()) {
                myEquations.add(equation);
            }
        }
    }

    // TODO: add a consistency check to ensure same # of equations per
    // dimension??

    // Example format:
    // [
    //  s -> [2 1 2 -1 3 0]
    //  prefixExponent -> [2 1 2 -1 3 0]
    //  rad -> [2 1 2 -1 3 0]
    //  deg -> [2 1 2 -1 3 0]
    //  m -> [2 1 2 -1 3 0]
    // ]
    @Override
    public String toString() {
        StringBuffer sb = new StringBuffer();
        sb.append("[" + System.lineSeparator());
        for (String key : eqSet.keySet()) {
            sb.append(" " + key + " -> [");
            sb.append(String.join(", ", eqSet.get(key).toString()));
            sb.append("]" + System.lineSeparator());
        }
        sb.append("]" + System.lineSeparator());
        return sb.toString();
    }

    @Override
    public int hashCode() {
        return HashCodeUtils.hash(eqSet);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null) return false;
        if (getClass() != obj.getClass()) return false;
        Z3EquationSet other = (Z3EquationSet) obj;
        return eqSet.equals(other.eqSet);
    }
}
