package units.solvers.backend.z3smt.encoder;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.IntNum;
import org.checkerframework.javacutil.Pair;
import units.representation.UnitsRepresentationUtils;
import units.solvers.backend.z3smt.representation.Z3InferenceUnit;

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

    // naive 1 hot encoding over the given BoolExprs
    // TODO: better algo:
    // http://www.cs.cmu.edu/~wklieber/papers/2007_efficient-cnf-encoding-for-selecting-1.pdf
    // public static BoolExpr mkChainXor(Context ctx, BoolExpr... args) {
    //
    // BoolExpr atLeastOne = ctx.mkOr(args);
    // BoolExpr atMostOne = ctx.mkTrue();
    // for (int i = 0; i < args.length - 1; i++) {
    // for (int j = i + 1; j < args.length; j++) {
    //                /* @formatter:off // this is for eclipse formatter */
    //                atMostOne = ctx.mkAnd(atMostOne,
    //                    ctx.mkOr(
    //                        ctx.mkNot(args[i]),
    //                        ctx.mkNot(args[j])
    //                    )
    //                );
    //                /* @formatter:on // this is for eclipse formatter */
    // }
    // }
    //
    // System.out.println("ALO " + atLeastOne.simplify().toString());
    // System.out.println("AMO " + atMostOne.simplify().toString());
    //
    // return ctx.mkAnd(atLeastOne, atMostOne);
    // }

    public static BoolExpr mkOneHot(Context ctx, BoolExpr arg1, BoolExpr arg2, BoolExpr arg3) {
        BoolExpr atLeastOne = ctx.mkOr(arg1, arg2, arg3);
        /* @formatter:off // this is for eclipse formatter */
        BoolExpr atMostOne =
                ctx.mkAnd(
                        ctx.mkOr(ctx.mkNot(arg1), ctx.mkNot(arg2)),
                        ctx.mkOr(ctx.mkNot(arg1), ctx.mkNot(arg3)),
                        ctx.mkOr(ctx.mkNot(arg2), ctx.mkNot(arg3)));
        /* @formatter:on // this is for eclipse formatter */
        BoolExpr result = ctx.mkAnd(atLeastOne, atMostOne);
        System.out.println("WF: (assert " + result.simplify().toString() + ")");
        return result;
    }

    /** Slot well-formedness constraint: that either uu = true, ub = true, or uu == ub = false */
    public static BoolExpr slotWellformedness(Context ctx, Z3InferenceUnit unit) {
        BoolExpr allPrefixesAreZero = allPrefixesAreZero(ctx, unit);
        /* @formatter:off // this is for eclipse formatter */
        return UnitsZ3SmtEncoderUtils.mkOneHot(
                ctx,
                ctx.mkAnd(ctx.mkNot(unit.getUnknownUnits()), ctx.mkNot(unit.getUnitsBottom())),
                ctx.mkAnd(unit.getUnknownUnits(), allPrefixesAreZero),
                ctx.mkAnd(unit.getUnitsBottom(), allPrefixesAreZero));
        /* @formatter:on // this is for eclipse formatter */
    }

    // TODO: more preferable to not have to encode exponent == 0 in
    // wellformedness, but currently we must do so in order to have exponent
    // variable declarations outputted for the z3 files
    // public static BoolExpr slotWellformedness(Context ctx, Z3InferenceUnit unit)
    // {
    //        /* @formatter:off // this is for eclipse formatter */
    //        return UnitsZ3SmtEncoderUtils.mkOneHot(
    //                ctx,
    //                ctx.mkAnd(ctx.mkNot(unit.getUnknownUnits()), ctx.mkNot(unit.getUnitsBottom())),
    //                unit.getUnknownUnits(),
    //                unit.getUnitsBottom());
    //        /* @formatter:on // this is for eclipse formatter */
    // }

    /** Slot preference constraint: that the slot == dimensionless */
    public static BoolExpr slotPreference(Context ctx, Z3InferenceUnit unit) {
        return mustBeDimensionless(ctx, unit);
    }

    private static BoolExpr allPrefixesAreZero(Context ctx, Z3InferenceUnit unit) {
        IntNum zero = ctx.mkInt(0);
        BoolExpr result = ctx.mkEq(unit.getPrefixExponent(), zero);
        for (String baseUnit : UnitsRepresentationUtils.getInstance().baseUnits()) {
            /* @formatter:off // this is for eclipse formatter */
            result = ctx.mkAnd(result, ctx.mkEq(unit.getExponent(baseUnit), zero));
            /* @formatter:on // this is for eclipse formatter */
        }
        return result;
    }

    private static BoolExpr mustBeDimensionless(Context ctx, Z3InferenceUnit unit) {
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

    // fst = snd iff the bool and int component values are equal
    // For Equality, and also Modulo
    public static BoolExpr equality(Context ctx, Z3InferenceUnit fst, Z3InferenceUnit snd) {
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
    public static BoolExpr subtype(Context ctx, Z3InferenceUnit subT, Z3InferenceUnit superT) {
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
            Context ctx, Z3InferenceUnit lhs, Z3InferenceUnit rhs, Z3InferenceUnit res) {
        // set lhs == rhs, and rhs == res, transitively lhs == res
        return ctx.mkAnd(equality(ctx, lhs, rhs), equality(ctx, rhs, res));
    }

    public static BoolExpr multiply(
            Context ctx, Z3InferenceUnit lhs, Z3InferenceUnit rhs, Z3InferenceUnit res) {
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

        /*
         * r = x * y
        x = top && r = top ||
        y = top && r = top ||

        */

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
            Context ctx, Z3InferenceUnit lhs, Z3InferenceUnit rhs, Z3InferenceUnit res) {
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
