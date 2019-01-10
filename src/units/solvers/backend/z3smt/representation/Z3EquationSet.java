package units.solvers.backend.z3smt.representation;

import com.microsoft.z3.BoolExpr;
import java.util.HashMap;
import java.util.Map;
import org.checkerframework.dataflow.util.HashCodeUtils;
import org.checkerframework.javacutil.BugInCF;
import units.representation.UnitsRepresentationUtils;

public class Z3EquationSet {

    // TODO: better shorter key names
    public static final String topAndBottomKey = "topAndBottom";
    public static final String prefixExponentKey = "prefixExponent";

    // Keys include topAndBottomKey
    // and potentially prefixExponentKey and the base units
    private final Map<String, BoolExpr> eqSet;

    public Z3EquationSet() {
        eqSet = new HashMap<>();
    }

    public BoolExpr getEquation(String key) {
        return eqSet.get(key);
    }

    public void addEquation(String key, BoolExpr equation) {
        // TODO: base unit set or serializableBaseUnits set?
        if (!(key == topAndBottomKey
                || key == prefixExponentKey
                || UnitsRepresentationUtils.getInstance().serializableBaseUnits().contains(key))) {
            throw new BugInCF("Trying to add an equation for unsupported key " + key);
        }

        if (eqSet.containsKey(key)) {
            throw new BugInCF("Trying to replace an equation " + key);
        }

        eqSet.put(key, equation);
    }

    // Example format:
    // [
    //  s -> [eq]
    //  prefixExponent -> [eq]
    //  rad -> [eq]
    //  deg -> [eq]
    //  m -> [eq]
    // ]
    @Override
    public String toString() {
        StringBuffer sb = new StringBuffer();
        sb.append("[" + System.lineSeparator());
        for (String key : eqSet.keySet()) {
            sb.append(" " + key + " -> [");
            sb.append(String.join(", ", eqSet.get(key).simplify().toString()));
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
