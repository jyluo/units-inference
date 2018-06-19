package units.util;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.IntNum;
import java.util.Arrays;
import java.util.List;
import org.checkerframework.javacutil.Pair;
import units.representation.InferenceUnit;
import units.representation.UnitsRepresentationUtils;

/**
 * Utility class with methods for defining z3 variable names and encoding of various relationships
 * between Units.
 */
public class UnitsZ3SmtEncoderUtils {

    private static final char idComponentSeparator = '-';
    public static final String uuSlotName = "TOP";
    public static final String ubSlotName = "BOT";
    public static final String prefixSlotName = "PREFIX";

    public static String z3VarName(int slotID, String component) {
        return slotID + String.valueOf(idComponentSeparator) + component;
    }

    public static Pair<Integer, String> slotFromZ3VarName(String z3VarName) {
        int dashIndex = z3VarName.indexOf(idComponentSeparator);

        int slotID;
        String component;

        if (dashIndex < 0) {
            slotID = Integer.valueOf(z3VarName);
            component = null;
        } else {
            slotID = Integer.valueOf(z3VarName.substring(0, dashIndex));
            component = z3VarName.substring(dashIndex + 1);
        }

        return Pair.of(slotID, component);
    }

    /** Slot well-formedness constraint: that either uu = true, ub = true, or uu == ub = false */
    public static BoolExpr slotWellformedness(Context ctx, InferenceUnit unit) {
        BoolExpr allPrefixesAreZero = allPrefixesAreZero(ctx, unit);
        /* @formatter:off // this is for eclipse formatter */
        return UnitsZ3SmtEncoderUtils.mkChainXor(
                ctx,
                ctx.mkAnd(ctx.mkNot(unit.getUnknownUnits()), ctx.mkNot(unit.getUnitsBottom())),
                ctx.mkAnd(unit.getUnknownUnits(), allPrefixesAreZero),
                ctx.mkAnd(unit.getUnitsBottom(), allPrefixesAreZero));
        /* @formatter:on // this is for eclipse formatter */
    }

    /** Slot preference constraint: that the slot == dimensionless */
    public static BoolExpr slotPreference(Context ctx, InferenceUnit unit) {
        return mustBeDimensionless(ctx, unit);
    }

    private static BoolExpr allPrefixesAreZero(Context ctx, InferenceUnit unit) {
        IntNum zero = ctx.mkInt(0);
        BoolExpr result = ctx.mkEq(unit.getPrefixExponent(), zero);
        for (String baseUnit : UnitsRepresentationUtils.getInstance().baseUnits()) {
            /* @formatter:off // this is for eclipse formatter */
            result = ctx.mkAnd(result, ctx.mkEq(unit.getExponent(baseUnit), zero));
            /* @formatter:on // this is for eclipse formatter */
        }
        return result;
    }

    private static BoolExpr mustBeDimensionless(Context ctx, InferenceUnit unit) {
        BoolExpr allPrefixesAreZero = allPrefixesAreZero(ctx, unit);
        /* @formatter:off // this is for eclipse formatter */
        return ctx.mkAnd(
                ctx.mkNot(unit.getUnknownUnits()),
                ctx.mkNot(unit.getUnitsBottom()),
                allPrefixesAreZero);
        /* @formatter:on // this is for eclipse formatter */
    }
    //
    //    private static BoolExpr mustBeUnknownUnits(Context ctx, InferenceUnit unit) {
    //        BoolExpr allPrefixesAreZero = allPrefixesAreZero(ctx, unit);
    //        /* @formatter:off // this is for eclipse formatter */
    //        return ctx.mkAnd(
    //                 unit.getUnknownUnits(),
    //                 ctx.mkNot(unit.getUnitsBottom()),
    //                 allPrefixesAreZero
    //               );
    //        /* @formatter:on // this is for eclipse formatter */
    //    }
    //
    //    private static BoolExpr mustBeUnitsBottom(Context ctx, InferenceUnit unit) {
    //        BoolExpr allPrefixesAreZero = allPrefixesAreZero(ctx, unit);
    //        /* @formatter:off // this is for eclipse formatter */
    //        return ctx.mkAnd(
    //                 ctx.mkNot(unit.getUnknownUnits()),
    //                 unit.getUnitsBottom(),
    //                 allPrefixesAreZero
    //               );
    //        /* @formatter:on // this is for eclipse formatter */
    //    }

    // =========================================================================================

    // xor is commutative and associative
    public static BoolExpr mkChainXor(
            Context ctx, BoolExpr arg0, BoolExpr arg1, BoolExpr... remainingArgs) {
        List<BoolExpr> argsList = Arrays.asList(remainingArgs);
        BoolExpr result = ctx.mkXor(arg0, arg1);

        for (BoolExpr arg : argsList) {
            result = ctx.mkXor(result, arg);
        }

        return result;
    }

    // fst = snd iff the bool and int component values are equal
    // For Equality, and also Modulo
    public static BoolExpr equality(Context ctx, InferenceUnit fst, InferenceUnit snd) {
        /* @formatter:off // this is for eclipse formatter */
        BoolExpr equalityEncoding =
                ctx.mkAnd(
                        ctx.mkEq(fst.getUnknownUnits(), snd.getUnknownUnits()),
                        ctx.mkEq(fst.getUnitsBottom(), snd.getUnitsBottom()),
                        ctx.mkEq(fst.getPrefixExponent(), snd.getPrefixExponent()));
        for (String baseUnit : UnitsRepresentationUtils.getInstance().baseUnits()) {
            equalityEncoding =
                    ctx.mkAnd(
                            equalityEncoding,
                            ctx.mkEq(fst.getExponent(baseUnit), snd.getExponent(baseUnit)));
        }
        /* @formatter:on // this is for eclipse formatter */
        return equalityEncoding;
    }

    // sub <: super has 5 cases:
    // sub = bot, or
    // super = top, or
    // sub = super
    public static BoolExpr subtype(Context ctx, InferenceUnit subT, InferenceUnit superT) {
        /* @formatter:off // this is for eclipse formatter */
        BoolExpr subtypeEncoding =
                ctx.mkOr(
                        // sub = bot
                        subT.getUnitsBottom(),
                        // super = top
                        superT.getUnknownUnits(),
                        // sub = super
                        equality(ctx, subT, superT));

        //            ctx.mkOr(
        //                // sub = top --> super = top
        //                ctx.mkAnd(subT.getUnknownUnits(), superT.getUnknownUnits()),
        //                // sub = bot
        //                subT.getUnitsBottom(),
        //                // super = top
        //                superT.getUnknownUnits(),
        //                // super = bot --> sub = bot
        //                ctx.mkAnd(superT.getUnitsBottom(), subT.getUnitsBottom()),
        //                // sub = super
        //                equality(ctx, subT, superT)
        //            );

        //            ctx.mkOr(
        //                // sub = top --> super = top
        //                ctx.mkAnd(mustBeUnknownUnits(ctx, subT), mustBeUnknownUnits(ctx, superT)),
        //                // sub = bot
        //                mustBeUnitsBottom(ctx, subT),
        //                // super = top
        //                mustBeUnknownUnits(ctx, superT),
        //                // super = bot --> sub = bot
        //                ctx.mkAnd(mustBeUnitsBottom(ctx, superT), mustBeUnitsBottom(ctx, subT)),
        //                // sub = super
        //                equality(ctx, subT, superT)
        //            );

        //            ctx.mkAnd(
        //                //ctx.mkImplies(arg0, arg1)
        //                // not (super = top or super = bottom) --> sub = super xor sub = bottom
        //                ctx.mkOr(
        //                    ctx.mkOr(
        //                        superT.getUnknownUnits(),
        //                        superT.getUnitsBottom()
        //                    ),
        //                    ctx.mkXor(equality(ctx, subT, superT), subT.getUnitsBottom())
        //                ),
        //                // super = bottom --> sub = bottom
        //                ctx.mkOr(
        //                    ctx.mkNot(
        //                        superT.getUnitsBottom()
        //                    ),
        //                    subT.getUnitsBottom()
        //                )
        //            );
        /* @formatter:on // this is for eclipse formatter */
        return subtypeEncoding;
    }

    // For Addition and Subtraction
    public static BoolExpr tripleEquality(
            Context ctx, InferenceUnit lhs, InferenceUnit rhs, InferenceUnit res) {
        // set lhs == rhs, and rhs == res, transitively lhs == res
        return ctx.mkAnd(equality(ctx, lhs, rhs), equality(ctx, rhs, res));
    }

    public static BoolExpr multiply(
            Context ctx, InferenceUnit lhs, InferenceUnit rhs, InferenceUnit res) {
        /* @formatter:off // this is for eclipse formatter */
        // Forall base units, r_exponent = lhs_exponent + rhs_exponent
        BoolExpr exponents = ctx.mkTrue();
        for (String baseUnit : UnitsRepresentationUtils.getInstance().baseUnits()) {
            exponents =
                    ctx.mkAnd(
                            exponents,
                            ctx.mkEq(
                                    res.getExponent(baseUnit),
                                    ctx.mkAdd(
                                            lhs.getExponent(baseUnit), rhs.getExponent(baseUnit))));
        }
        BoolExpr multiplyEncoding =
                // res component = lhs component + rhs component
                ctx.mkAnd(
                        ctx.mkEq(
                                res.getUnknownUnits(),
                                ctx.mkOr(lhs.getUnknownUnits(), rhs.getUnknownUnits())),
                        ctx.mkEq(
                                res.getUnitsBottom(),
                                ctx.mkOr(lhs.getUnitsBottom(), rhs.getUnitsBottom())),
                        ctx.mkEq(
                                res.getPrefixExponent(),
                                ctx.mkAdd(lhs.getPrefixExponent(), rhs.getPrefixExponent())),
                        exponents);
        /* @formatter:on // this is for eclipse formatter */
        return multiplyEncoding;
    }

    public static BoolExpr divide(
            Context ctx, InferenceUnit lhs, InferenceUnit rhs, InferenceUnit res) {
        /* @formatter:off // this is for eclipse formatter */
        // Forall base units, r_exponent = lhs_exponent - rhs_exponent
        BoolExpr exponents = ctx.mkTrue();
        for (String baseUnit : UnitsRepresentationUtils.getInstance().baseUnits()) {
            exponents =
                    ctx.mkAnd(
                            exponents,
                            ctx.mkEq(
                                    res.getExponent(baseUnit),
                                    ctx.mkSub(
                                            lhs.getExponent(baseUnit), rhs.getExponent(baseUnit))));
        }
        BoolExpr divideEncoding =
                // res component = lhs component + rhs component
                ctx.mkAnd(
                        ctx.mkEq(
                                res.getUnknownUnits(),
                                ctx.mkOr(lhs.getUnknownUnits(), rhs.getUnknownUnits())),
                        ctx.mkEq(
                                res.getUnitsBottom(),
                                ctx.mkOr(lhs.getUnitsBottom(), rhs.getUnitsBottom())),
                        ctx.mkEq(
                                res.getPrefixExponent(),
                                ctx.mkSub(lhs.getPrefixExponent(), rhs.getPrefixExponent())),
                        exponents);
        /* @formatter:on // this is for eclipse formatter */
        return divideEncoding;
    }
}
