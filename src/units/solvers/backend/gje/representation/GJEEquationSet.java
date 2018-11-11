package units.solvers.backend.gje.representation;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import org.checkerframework.dataflow.util.HashCodeUtils;
import org.checkerframework.javacutil.BugInCF;
import units.representation.UnitsRepresentationUtils;

public class GJEEquationSet {

    public static final String prefixExponentKey = "prefixExponent";

    // for representing a contradictory outcome of an encoded constraint that
    // contains constant-constant pairs
    // TODO: set this too by adding incompatible equations??
    private boolean isContradiction;

    // Map<Dimension, Set<Equation>>
    private final Map<String, Set<String>> eqSet = new HashMap<>();

    public GJEEquationSet() {
        this(false);
    }

    public GJEEquationSet(boolean isContradiction) {
        this.isContradiction = isContradiction;
    }

    public Map<String, Set<String>> getEquationSet() {
        return eqSet;
    }

    public boolean isEmpty() {
        return eqSet.isEmpty();
    }

    public boolean isContradiction() {
        return isContradiction;
    }

    public void addEquation(String key, String equation) {
        if (!(key == prefixExponentKey
                || UnitsRepresentationUtils.getInstance().baseUnits().contains(key))) {
            throw new BugInCF("Trying to add an equation for unsupported key " + key);
        }

        if (!eqSet.containsKey(key)) {
            eqSet.put(key, new HashSet<>());
        }

        eqSet.get(key).add(equation);
    }

    public void union(GJEEquationSet otherSet) {
        isContradiction = isContradiction || otherSet.isContradiction;

        for (Entry<String, Set<String>> otherEntry : otherSet.eqSet.entrySet()) {
            String key = otherEntry.getKey();
            if (!eqSet.containsKey(key)) {
                eqSet.put(key, new HashSet<>());
            }
            Set<String> myEquations = eqSet.get(key);
            for (String equation : otherEntry.getValue()) {
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
        if (isContradiction) {
            sb.append("contradiction");
        } else {
            for (String key : eqSet.keySet()) {
                sb.append(" " + key + " -> [");
                sb.append(String.join(", ", eqSet.get(key)));
                sb.append("]" + System.lineSeparator());
            }
        }
        sb.append("]" + System.lineSeparator());
        return sb.toString();
    }

    @Override
    public int hashCode() {
        return HashCodeUtils.hash(isContradiction, eqSet);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null) return false;
        if (getClass() != obj.getClass()) return false;
        GJEEquationSet other = (GJEEquationSet) obj;
        return isContradiction == other.isContradiction && eqSet.equals(other.eqSet);
    }
}
