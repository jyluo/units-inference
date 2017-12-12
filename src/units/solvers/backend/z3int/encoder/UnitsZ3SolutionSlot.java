package units.solvers.backend.z3int.encoder;

import java.util.HashMap;
import java.util.Map;
import units.util.UnitsUtils;

public class UnitsZ3SolutionSlot {
    private final int slotID;

    private boolean uu;
    private boolean ub;

    private int prefixExponent;

    private final Map<String, Integer> exponents;

    public UnitsZ3SolutionSlot(int slotID) {
        this.slotID = slotID;
        exponents = new HashMap<>();

        // default UU value is false
        uu = false;
        // default UU value is false
        ub = false;
        // default prefixExponent is 0
        prefixExponent = 0;

        for (String baseUnit : UnitsUtils.baseUnits()) {
            // default exponents are 0
            exponents.put(baseUnit, 0);
        }
    }

    public void setUnknownUnits(boolean val) {
        uu = val;
    }

    public boolean getUnknownUnits() {
        return uu;
    }

    public void setUnitsBottom(boolean val) {
        ub = val;
    }

    public boolean getUnitsBottom() {
        return ub;
    }

    public void setPrefixExponent(int exp) {
        prefixExponent = exp;
    }

    public int getPrefixExponent() {
        return prefixExponent;
    }

    public void setExponent(String unit, int exp) {
        assert exponents.containsKey(unit);
        exponents.replace(unit, exp);
    }

    public int getExponent(String unit) {
        assert exponents.containsKey(unit);
        return exponents.get(unit);
    }

    public Map<String, Integer> getExponents() {
        return exponents;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((exponents == null) ? 0 : exponents.hashCode());
        result = prime * result + prefixExponent;
        result = prime * result + slotID;
        result = prime * result + (ub ? 1231 : 1237);
        result = prime * result + (uu ? 1231 : 1237);
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        UnitsZ3SolutionSlot other = (UnitsZ3SolutionSlot) obj;
        if (exponents == null) {
            if (other.exponents != null)
                return false;
        } else if (!exponents.equals(other.exponents))
            return false;
        if (prefixExponent != other.prefixExponent)
            return false;
        if (slotID != other.slotID)
            return false;
        if (ub != other.ub)
            return false;
        if (uu != other.uu)
            return false;
        return true;
    }
}
