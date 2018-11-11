package units.solvers.backend.gje.encoder;

import java.util.Map;
import java.util.Set;
import org.checkerframework.javacutil.BugInCF;
import units.solvers.backend.gje.representation.GJEInferenceUnit;

/**
 * Utility class with methods for defining z3 variable names and encoding of various relationships
 * between Units.
 */
public class UnitsGJEEncoderUtils {

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
    public static Map<String, Set<String>> equality(GJEInferenceUnit fst, GJEInferenceUnit snd) {
        if (fst.isConstant() && snd.isConstant() && !fst.equals(snd)) {
            throw new BugInCF(
                    "trying to encode an always false equality constraint: " + fst + " == " + snd);
        }

        // this needs to return 8 strings for pair-wise equality
        // TODO: return 1 equation per dimension
        // Map<dimension, list<equation>> ??

        //        if (fst.isConstant() && snd.isVariable()) {
        //            // input: eg x = 3
        //            // output: 1 1 ID 3
        //            return String.join(
        //                    " ",
        //                    "1",
        //                    "1",
        //                    String.valueOf(snd.getGJESlotID()),
        //                    String.valueOf(fst.getPrefixExponent()));
        //        }

        // 3 cases
        return null;
    }

    // sub <: super has 5 cases:
    // sub = bot, or
    // super = top, or
    // sub = super
    public static Map<String, Set<String>> subtype(GJEInferenceUnit subT, GJEInferenceUnit superT) {
        return equality(subT, superT);
    }

    // For Addition and Subtraction
    public static Map<String, Set<String>> tripleEquality(
            GJEInferenceUnit lhs, GJEInferenceUnit rhs, GJEInferenceUnit res) {

        // TODO: return 2 equations per dimension
        return null;

        // set lhs == rhs, and rhs == res, transitively lhs == res
        // return ctx.mkAnd(equality(ctx, lhs, rhs), equality(ctx, rhs, res));
    }

    public static Map<String, Set<String>> multiply(
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
