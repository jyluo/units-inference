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

    // private static String allPrefixesAreZero(GJEInferenceUnit unit) {
    // IntNum zero = ctx.mkInt(0);
    // String result = ctx.mkEq(unit.getPrefixExponent(), zero);
    // for (String baseUnit :
    // UnitsRepresentationUtils.getInstance().baseUnits()) {
    // /* @formatter:off // this is for eclipse formatter */
    // result = ctx.mkAnd(result, ctx.mkEq(unit.getExponent(baseUnit), zero));
    // /* @formatter:on // this is for eclipse formatter */
    // }
    // return result;
    // }
    //
    // private static String mustBeDimensionless(GJEInferenceUnit unit) {
    // String allPrefixesAreZero = allPrefixesAreZero(ctx, unit);
    // /* @formatter:off // this is for eclipse formatter */
    // return ctx.mkAnd(
    // ctx.mkNot(unit.getUnknownUnits()),
    // ctx.mkNot(unit.getUnitsBottom()),
    // allPrefixesAreZero);
    // /* @formatter:on // this is for eclipse formatter */
    // }
    //
    // =========================================================================================

    // fst = snd iff the bool and int component values are equal
    // For Equality, and also Modulo
    public static GJEEquationSet equality(GJEInferenceUnit fst, GJEInferenceUnit snd) {
        if (fst.isConstant() && snd.isConstant() && !fst.equals(snd)) {
            throw new BugInCF(
                    "trying to encode an always false equality constraint: " + fst + " == " + snd);
        }

        // returns 1 + |baseUnits| equation strings for pair-wise equality
        if (fst.isConstant() && snd.isVariable()) {
            return equalityCV(fst, snd);
        } else if (fst.isVariable() && snd.isConstant()) {
            return equalityCV(snd, fst);
        } else {
            // both are variables
            GJEEquationSet eqSet = new GJEEquationSet();
            // input: eg x = y (aka x - y = 0)
            // output: 2 1 IDx -1 IDy 0
            String prefixExponentEq =
                    String.join(
                            delimiter,
                            "2",
                            "1",
                            String.valueOf(fst.getGJEVarID()),
                            "-1",
                            String.valueOf(snd.getGJEVarID()),
                            "0");
            // System.out.println(" prefixEx eq: " + prefixExponentEq);
            eqSet.addEquation(GJEEquationSet.prefixExponentKey, prefixExponentEq);

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
        String prefixExponentEq =
                String.join(
                        delimiter,
                        "1",
                        "1",
                        String.valueOf(variable.getGJEVarID()),
                        String.valueOf(constant.getPrefixExponent()));
        // System.out.println(" prefixEx eq: " + prefixExponentEq);
        eqSet.addEquation(GJEEquationSet.prefixExponentKey, prefixExponentEq);

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

    // sub <: super has 5 cases:
    // sub = bot, or
    // super = top, or
    // sub = super
    public static GJEEquationSet subtype(GJEInferenceUnit subT, GJEInferenceUnit superT) {
        return equality(subT, superT);
    }

    // For Addition and Subtraction
    public static GJEEquationSet tripleEquality(
            GJEInferenceUnit lhs, GJEInferenceUnit rhs, GJEInferenceUnit res) {

        // set lhs == rhs, and rhs == res, transitively lhs == res
        GJEEquationSet eqSet = equality(lhs, rhs);
        eqSet.union(equality(rhs, res));

        System.out.println(eqSet);
        return eqSet;
    }

    public static GJEEquationSet multiply(
            GJEInferenceUnit lhs, GJEInferenceUnit rhs, GJEInferenceUnit res) {

        // TODO: return 1 equation per dimension
        return null;

        // /* @formatter:off // this is for eclipse formatter */
        // // Forall base units, r_exponent = lhs_exponent + rhs_exponent
        // String exponents = ctx.mkTrue();
        // for (String baseUnit :
        // UnitsRepresentationUtils.getInstance().baseUnits()) {
        // exponents =
        // ctx.mkAnd(
        // exponents,
        // ctx.mkEq(
        // res.getExponent(baseUnit),
        // ctx.mkAdd(
        // lhs.getExponent(baseUnit), rhs.getExponent(baseUnit))));
        // }
        // String multiplyEncoding =
        // // res component = lhs component + rhs component
        // ctx.mkAnd(
        // ctx.mkEq(
        // res.getUnknownUnits(),
        // ctx.mkOr(lhs.getUnknownUnits(), rhs.getUnknownUnits())),
        // ctx.mkEq(
        // res.getUnitsBottom(),
        // ctx.mkOr(lhs.getUnitsBottom(), rhs.getUnitsBottom())),
        // ctx.mkEq(
        // res.getPrefixExponent(),
        // ctx.mkAdd(lhs.getPrefixExponent(), rhs.getPrefixExponent())),
        // exponents);
        // /* @formatter:on // this is for eclipse formatter */
        // return multiplyEncoding;
    }

    public static String divide(GJEInferenceUnit lhs, GJEInferenceUnit rhs, GJEInferenceUnit res) {

        // TODO: return 1 equation per dimension
        return null;

        // /* @formatter:off // this is for eclipse formatter */
        // // Forall base units, r_exponent = lhs_exponent - rhs_exponent
        // String exponents = ctx.mkTrue();
        // for (String baseUnit :
        // UnitsRepresentationUtils.getInstance().baseUnits()) {
        // exponents =
        // ctx.mkAnd(
        // exponents,
        // ctx.mkEq(
        // res.getExponent(baseUnit),
        // ctx.mkSub(
        // lhs.getExponent(baseUnit), rhs.getExponent(baseUnit))));
        // }
        // String divideEncoding =
        // // res component = lhs component + rhs component
        // ctx.mkAnd(
        // ctx.mkEq(
        // res.getUnknownUnits(),
        // ctx.mkOr(lhs.getUnknownUnits(), rhs.getUnknownUnits())),
        // ctx.mkEq(
        // res.getUnitsBottom(),
        // ctx.mkOr(lhs.getUnitsBottom(), rhs.getUnitsBottom())),
        // ctx.mkEq(
        // res.getPrefixExponent(),
        // ctx.mkSub(lhs.getPrefixExponent(), rhs.getPrefixExponent())),
        // exponents);
        // /* @formatter:on // this is for eclipse formatter */
        // return divideEncoding;
    }
}
