package units.solvers.backend.gje.encoder;

import org.checkerframework.javacutil.BugInCF;
import units.representation.UnitsRepresentationUtils;
import units.solvers.backend.gje.representation.GJEEquationSet;
import units.solvers.backend.gje.representation.GJEInferenceUnit;

/**
 * Utility class with methods for defining z3 variable names and encoding of various relationships
 * between Units.
 */
public class UnitsGJEEncoderUtils {

    private static final String delimiter = " ";

    // For Equality, and also Modulo
    public static GJEEquationSet equality(GJEInferenceUnit fst, GJEInferenceUnit snd) {
        if (fst.isConstant() && snd.isConstant() && !fst.equals(snd)) {
            throw new BugInCF(
                    "trying to encode an always false equality constraint: " + fst + " == " + snd);
        }

        // returns 1 + |baseUnits| equations for pair-wise equality
        if (fst.isConstant() && snd.isVariable()) {
            return equalityCV(fst, snd);
        } else if (fst.isVariable() && snd.isConstant()) {
            return equalityCV(snd, fst);
        } else {
            // both are variables
            GJEEquationSet eqSet = new GJEEquationSet();
            // input: eg x = y (aka x - y = 0)
            // output: 2 1 IDx -1 IDy 0
            eqSet.addEquation(
                    GJEEquationSet.prefixExponentKey,
                    String.join(
                            delimiter,
                            "2",
                            "1",
                            String.valueOf(fst.getGJEVarID()),
                            "-1",
                            String.valueOf(snd.getGJEVarID()),
                            "0"));

            for (String baseUnit : UnitsRepresentationUtils.getInstance().baseUnits()) {
                eqSet.addEquation(
                        baseUnit,
                        String.join(
                                delimiter,
                                "2",
                                "1",
                                String.valueOf(fst.getGJEVarID()),
                                "-1",
                                String.valueOf(snd.getGJEVarID()),
                                "0"));
            }
            return eqSet;
        }
    }

    private static GJEEquationSet equalityCV(GJEInferenceUnit constant, GJEInferenceUnit variable) {
        GJEEquationSet eqSet = new GJEEquationSet();
        // input: eg 3 = x
        // output: 1 1 IDx 3
        eqSet.addEquation(
                GJEEquationSet.prefixExponentKey,
                String.join(
                        delimiter,
                        "1",
                        "1",
                        String.valueOf(variable.getGJEVarID()),
                        String.valueOf(constant.getPrefixExponent())));

        for (String baseUnit : UnitsRepresentationUtils.getInstance().baseUnits()) {
            eqSet.addEquation(
                    baseUnit,
                    String.join(
                            delimiter,
                            "1",
                            "1",
                            String.valueOf(variable.getGJEVarID()),
                            String.valueOf(constant.getExponent(baseUnit))));
        }
        return eqSet;
    }

    public static GJEEquationSet subtype(GJEInferenceUnit subT, GJEInferenceUnit superT) {
        return equality(subT, superT);
    }

    // For Addition and Subtraction
    public static GJEEquationSet tripleEquality(
            GJEInferenceUnit lhs, GJEInferenceUnit rhs, GJEInferenceUnit res) {

        // set lhs == rhs, and rhs == res, transitively lhs == res
        GJEEquationSet eqSet = equality(lhs, rhs);
        eqSet.union(equality(rhs, res));
        return eqSet;
    }

    public static GJEEquationSet multiply(
            GJEInferenceUnit lhs, GJEInferenceUnit rhs, GJEInferenceUnit res) {

        assert res.isVariable();

        // returns 1 + |baseUnits| equations

        // cases deemed impossible, because result is always a fresh variable:
        // c1 * c2 = c3 // contra or always true
        // c1 * v = c2 ==> exponents v = (c2 - c1)
        // v * c1 = c2 same
        // v1 * v2 = c1 ==> exponents v1 + v2 = c1

        // cases deemed possible:
        if (lhs.isConstant() && rhs.isConstant()) {
            // c1 * c2 = v ==> exponents v = (c1 + c2)
            GJEEquationSet eqSet = new GJEEquationSet();
            // input: eg c1 * c2 = v
            // output: 1 1 IDv (c1 + c2)
            eqSet.addEquation(
                    GJEEquationSet.prefixExponentKey,
                    String.join(
                            delimiter,
                            "1",
                            "1",
                            String.valueOf(res.getGJEVarID()),
                            String.valueOf(lhs.getPrefixExponent() + rhs.getPrefixExponent())));

            for (String baseUnit : UnitsRepresentationUtils.getInstance().baseUnits()) {
                eqSet.addEquation(
                        baseUnit,
                        String.join(
                                delimiter,
                                "1",
                                "1",
                                String.valueOf(res.getGJEVarID()),
                                String.valueOf(
                                        lhs.getExponent(baseUnit) + rhs.getExponent(baseUnit))));
            }
            return eqSet;

        } else if (lhs.isConstant() && rhs.isVariable()) {
            // c1 * v1 = v2 ==> exponents v2 - v1 = c1
            return multiplyCV(lhs, rhs, res);

        } else if (lhs.isVariable() && rhs.isConstant()) {
            // v1 * c1 = v2 same
            return multiplyCV(rhs, lhs, res);

        } else if (lhs.isVariable() && rhs.isVariable()) {
            // v1 * v2 = v3 ==> exponents v1 + v2 - v3 = 0
            GJEEquationSet eqSet = new GJEEquationSet();
            // input: eg v1 * v2 = v3
            // output: 3 1 IDv1 1 IDv2 -1 IDv3 0
            eqSet.addEquation(
                    GJEEquationSet.prefixExponentKey,
                    String.join(
                            delimiter,
                            "3",
                            "1",
                            String.valueOf(lhs.getGJEVarID()),
                            "1",
                            String.valueOf(rhs.getGJEVarID()),
                            "-1",
                            String.valueOf(res.getGJEVarID()),
                            "0"));

            for (String baseUnit : UnitsRepresentationUtils.getInstance().baseUnits()) {
                eqSet.addEquation(
                        baseUnit,
                        String.join(
                                delimiter,
                                "3",
                                "1",
                                String.valueOf(lhs.getGJEVarID()),
                                "1",
                                String.valueOf(rhs.getGJEVarID()),
                                "-1",
                                String.valueOf(res.getGJEVarID()),
                                "0"));
            }
            return eqSet;

        } else {
            throw new BugInCF(
                    "Encoding a multiplication case which is unsupported: "
                            + lhs
                            + " * "
                            + rhs
                            + " = "
                            + res);
        }
    }

    private static GJEEquationSet multiplyCV(
            GJEInferenceUnit constant, GJEInferenceUnit variable, GJEInferenceUnit res) {

        GJEEquationSet eqSet = new GJEEquationSet();
        // c1 * v1 = v2 ==> exponents v2 - v1 = c1
        // input: eg c1 * v1 = v2
        // output: 2 1 IDv2 -1 IDv1 c1
        eqSet.addEquation(
                GJEEquationSet.prefixExponentKey,
                String.join(
                        delimiter,
                        "2",
                        "1",
                        String.valueOf(res.getGJEVarID()),
                        "-1",
                        String.valueOf(variable.getGJEVarID()),
                        String.valueOf(constant.getPrefixExponent())));

        for (String baseUnit : UnitsRepresentationUtils.getInstance().baseUnits()) {
            eqSet.addEquation(
                    baseUnit,
                    String.join(
                            delimiter,
                            "2",
                            "1",
                            String.valueOf(res.getGJEVarID()),
                            "-1",
                            String.valueOf(variable.getGJEVarID()),
                            String.valueOf(constant.getExponent(baseUnit))));
        }
        return eqSet;
    }

    public static GJEEquationSet divide(
            GJEInferenceUnit lhs, GJEInferenceUnit rhs, GJEInferenceUnit res) {

        assert res.isVariable();

        // returns 1 + |baseUnits| equations

        // cases deemed impossible, because result is always a fresh variable:
        // c1 / c2 = c3 // contra or always true
        // c1 / v = c2 ==> c1 / c2 = v ==> exponents v = (c1 - c2)
        // v / c1 = c2 ==> exponents v = (c1 + c2)
        // v1 / v2 = c1 ==> exponents v1 - v2 = c1

        // cases deemed possible:
        if (lhs.isConstant() && rhs.isConstant()) {
            // c1 / c2 = v ==> exponents v = (c1 - c2)
            GJEEquationSet eqSet = new GJEEquationSet();
            // input: eg c1 / c2 = v
            // output: 1 1 IDv (c1 - c2)
            eqSet.addEquation(
                    GJEEquationSet.prefixExponentKey,
                    String.join(
                            delimiter,
                            "1",
                            "1",
                            String.valueOf(res.getGJEVarID()),
                            String.valueOf(lhs.getPrefixExponent() - rhs.getPrefixExponent())));

            for (String baseUnit : UnitsRepresentationUtils.getInstance().baseUnits()) {
                eqSet.addEquation(
                        baseUnit,
                        String.join(
                                delimiter,
                                "1",
                                "1",
                                String.valueOf(res.getGJEVarID()),
                                String.valueOf(
                                        lhs.getExponent(baseUnit) - rhs.getExponent(baseUnit))));
            }
            return eqSet;

        } else if (lhs.isConstant() && rhs.isVariable()) {
            // c1 / v1 = v2 ==> c1 = v2 * v1 ==> exponents v1 + v2 = c1
            GJEEquationSet eqSet = new GJEEquationSet();
            // input: eg c1 / v1 = v2
            // output: 2 1 IDv1 1 IDv2 c1
            eqSet.addEquation(
                    GJEEquationSet.prefixExponentKey,
                    String.join(
                            delimiter,
                            "2",
                            "1",
                            String.valueOf(rhs.getGJEVarID()),
                            "1",
                            String.valueOf(res.getGJEVarID()),
                            String.valueOf(lhs.getPrefixExponent())));

            for (String baseUnit : UnitsRepresentationUtils.getInstance().baseUnits()) {
                eqSet.addEquation(
                        baseUnit,
                        String.join(
                                delimiter,
                                "2",
                                "1",
                                String.valueOf(rhs.getGJEVarID()),
                                "1",
                                String.valueOf(res.getGJEVarID()),
                                String.valueOf(lhs.getExponent(baseUnit))));
            }
            return eqSet;

        } else if (lhs.isVariable() && rhs.isConstant()) {
            // v1 / c1 = v2 ==> v1 = v2 * c1 ==> v1 / v2 = c1 ==> exponents v1 - v2 = c1
            GJEEquationSet eqSet = new GJEEquationSet();
            // input: eg v1 / c1 = v2
            // output: 2 1 IDv1 -1 IDv2 c1
            eqSet.addEquation(
                    GJEEquationSet.prefixExponentKey,
                    String.join(
                            delimiter,
                            "2",
                            "1",
                            String.valueOf(lhs.getGJEVarID()),
                            "-1",
                            String.valueOf(res.getGJEVarID()),
                            String.valueOf(rhs.getPrefixExponent())));

            for (String baseUnit : UnitsRepresentationUtils.getInstance().baseUnits()) {
                eqSet.addEquation(
                        baseUnit,
                        String.join(
                                delimiter,
                                "2",
                                "1",
                                String.valueOf(lhs.getGJEVarID()),
                                "-1",
                                String.valueOf(res.getGJEVarID()),
                                String.valueOf(rhs.getExponent(baseUnit))));
            }
            return eqSet;

        } else if (lhs.isVariable() && rhs.isVariable()) {
            // v1 / v2 = v3 ==> exponents v1 - v2 - v3 = 0
            GJEEquationSet eqSet = new GJEEquationSet();
            // input: eg v1 / v2 = v3
            // output: 3 1 IDv1 -1 IDv2 -1 IDv3 0
            eqSet.addEquation(
                    GJEEquationSet.prefixExponentKey,
                    String.join(
                            delimiter,
                            "3",
                            "1",
                            String.valueOf(lhs.getGJEVarID()),
                            "-1",
                            String.valueOf(rhs.getGJEVarID()),
                            "-1",
                            String.valueOf(res.getGJEVarID()),
                            "0"));

            for (String baseUnit : UnitsRepresentationUtils.getInstance().baseUnits()) {
                eqSet.addEquation(
                        baseUnit,
                        String.join(
                                delimiter,
                                "3",
                                "1",
                                String.valueOf(lhs.getGJEVarID()),
                                "-1",
                                String.valueOf(rhs.getGJEVarID()),
                                "-1",
                                String.valueOf(res.getGJEVarID()),
                                "0"));
            }
            return eqSet;

        } else {
            throw new BugInCF(
                    "Encoding a division case which is unsupported: "
                            + lhs
                            + " / "
                            + rhs
                            + " = "
                            + res);
        }
    }
}
