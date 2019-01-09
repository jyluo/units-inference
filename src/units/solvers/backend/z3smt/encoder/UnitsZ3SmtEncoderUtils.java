package units.solvers.backend.z3smt.encoder;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.IntNum;
import org.checkerframework.javacutil.Pair;
import units.representation.UnitsRepresentationUtils;
import units.solvers.backend.z3smt.representation.Z3EquationSet;
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
    // System.err.println("ALO " + atLeastOne.simplify().toString());
    // System.err.println("AMO " + atMostOne.simplify().toString());
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
        // System.err.println("WF: (assert " + result.simplify().toString() + ")");
        return result;
    }

    /** Slot well-formedness constraint: that either uu = true, ub = true, or uu == ub = false */
    public static BoolExpr slotWellformedness(Context ctx, Z3InferenceUnit unit) {
        // for GJE experiment
        // return ctx.mkAnd(ctx.mkNot(unit.getUnknownUnits()),
        // ctx.mkNot(unit.getUnitsBottom()));

        // truthtable xor (xor ((not x and not y), x), y)
        // TODO: more preferable to not have to encode exponent == 0 in
        // wellformedness, but currently we must do so in order to have exponent
        // variable declarations outputted for the z3 files
        BoolExpr allExponentsAreZero = allExponentsAreZero(ctx, unit);
        /* @formatter:off // this is for eclipse formatter */
        return UnitsZ3SmtEncoderUtils.mkOneHot(
                ctx,
                ctx.mkAnd(ctx.mkNot(unit.getUnknownUnits()), ctx.mkNot(unit.getUnitsBottom())),
                ctx.mkAnd(unit.getUnknownUnits(), allExponentsAreZero),
                ctx.mkAnd(unit.getUnitsBottom(), allExponentsAreZero));
        /* @formatter:on // this is for eclipse formatter */

        // simplify xor (xor ((not x and not y), x), y)
        // // Simplified version:
        // return ctx.mkNot(ctx.mkAnd(unit.getUnknownUnits(), unit.getUnitsBottom()));
        // return ctx.mkOr(ctx.mkNot(unit.getUnknownUnits()), ctx.mkNot(unit.getUnitsBottom()));
    }

    /** Slot preference constraint: that the slot == dimensionless */
    public static BoolExpr slotPreference(Context ctx, Z3InferenceUnit unit) {
        return mustBeDimensionless(ctx, unit);
    }

    private static BoolExpr allExponentsAreZero(Context ctx, Z3InferenceUnit unit) {
        IntNum zero = ctx.mkInt(0);
        BoolExpr result = ctx.mkTrue();
        if (UnitsRepresentationUtils.getInstance().serializePrefix()) {
            result = ctx.mkEq(unit.getPrefixExponent(), zero);
        }
        for (String baseUnit : UnitsRepresentationUtils.getInstance().serializableBaseUnits()) {
            /* @formatter:off // this is for eclipse formatter */
            result = ctx.mkAnd(result, ctx.mkEq(unit.getExponent(baseUnit), zero));
            /* @formatter:on // this is for eclipse formatter */
        }
        return result;
    }

    private static BoolExpr mustBeDimensionless(Context ctx, Z3InferenceUnit unit) {
        BoolExpr allExponentsAreZero = allExponentsAreZero(ctx, unit);
        /* @formatter:off // this is for eclipse formatter */
        return ctx.mkAnd(
                ctx.mkNot(unit.getUnknownUnits()),
                ctx.mkNot(unit.getUnitsBottom()),
                allExponentsAreZero);
        /* @formatter:on // this is for eclipse formatter */
    }

    // =========================================================================================

    // fst = snd iff the bool and int component values are equal
    // For Equality, and also Modulo
    public static Z3EquationSet equality(Context ctx, Z3InferenceUnit fst, Z3InferenceUnit snd) {
        /* @formatter:off // this is for eclipse formatter */
        BoolExpr equalityEncoding =
                ctx.mkAnd(
                        ctx.mkEq(fst.getUnknownUnits(), snd.getUnknownUnits()),
                        ctx.mkEq(fst.getUnitsBottom(), snd.getUnitsBottom()));
        if (UnitsRepresentationUtils.getInstance().serializePrefix()) {
            equalityEncoding =
                    ctx.mkAnd(
                            equalityEncoding,
                            ctx.mkEq(fst.getPrefixExponent(), snd.getPrefixExponent()));
        }
        for (String baseUnit : UnitsRepresentationUtils.getInstance().serializableBaseUnits()) {
            equalityEncoding =
                    ctx.mkAnd(
                            equalityEncoding,
                            ctx.mkEq(fst.getExponent(baseUnit), snd.getExponent(baseUnit)));
        }
        /* @formatter:on // this is for eclipse formatter */
        return equalityEncoding;
    }

    // sub <: super has 6 cases:
    // bot <: bot
    // bot <: x
    // bot <: top
    // x <: top
    // top <: top
    // x <: x
    public static Z3EquationSet subtype(Context ctx, Z3InferenceUnit subT, Z3InferenceUnit superT) {
        /* @formatter:off // this is for eclipse formatter */
        BoolExpr subtypeEncoding =
                ctx.mkOr(
                        // sub = bot
                        subT.getUnitsBottom(),
                        // super = top
                        superT.getUnknownUnits(),
                        // if neither is top or bottom then they must be equal: sub = super
                        ctx.mkAnd(
                                ctx.mkNot(subT.getUnknownUnits()),
                                ctx.mkNot(subT.getUnitsBottom()),
                                ctx.mkNot(superT.getUnknownUnits()),
                                ctx.mkNot(superT.getUnitsBottom()),
                                equality(ctx, subT, superT)));
        /* @formatter:on // this is for eclipse formatter */
        return subtypeEncoding;

        // old subtype encoding, which potentially enforced equality even when unnecessary
        // ctx.mkOr(
        //   // sub = bot
        //   subT.getUnitsBottom(),
        //   // super = top
        //   superT.getUnknownUnits(),
        //   // sub = super
        //   equality(ctx, subT, superT));
    }

    // For Addition and Subtraction
    public static Z3EquationSet tripleEquality(
            Context ctx, Z3InferenceUnit lhs, Z3InferenceUnit rhs, Z3InferenceUnit res) {
        // set lhs == rhs, and rhs == res, transitively lhs == res
        return ctx.mkAnd(equality(ctx, lhs, rhs), equality(ctx, rhs, res));
    }

    public static Z3EquationSet comparable(Context ctx, Z3InferenceUnit fst, Z3InferenceUnit snd) {

        // fst <: snd or snd <: fst
        return ctx.mkOr(
                UnitsZ3SmtEncoderUtils.subtype(ctx, fst, snd),
                UnitsZ3SmtEncoderUtils.subtype(ctx, snd, fst));
    }

    public static Z3EquationSet addSub(
            Context ctx, Z3InferenceUnit lhs, Z3InferenceUnit rhs, Z3InferenceUnit res) {
        return ctx.mkAnd(
                UnitsZ3SmtEncoderUtils.subtype(ctx, lhs, res),
                UnitsZ3SmtEncoderUtils.subtype(ctx, rhs, res));

        // // 3 way equality (ie leftOperand == rightOperand, and rightOperand == result).
        // return UnitsZ3SmtEncoderUtils.tripleEquality(ctx,
        // leftOperand.serialize(z3SmtFormatTranslator),
        // rightOperand.serialize(z3SmtFormatTranslator),
        // result.serialize(z3SmtFormatTranslator));
    }

    public static Z3EquationSet multiply(
            Context ctx, Z3InferenceUnit lhs, Z3InferenceUnit rhs, Z3InferenceUnit res) {
        /* @formatter:off // this is for eclipse formatter */
        // Forall base units, r_exponent = lhs_exponent + rhs_exponent

        BoolExpr exponents = ctx.mkTrue();
        if (UnitsRepresentationUtils.getInstance().serializePrefix()) {
            exponents =
                    ctx.mkEq(
                            res.getPrefixExponent(),
                            ctx.mkAdd(lhs.getPrefixExponent(), rhs.getPrefixExponent()));
        }
        for (String baseUnit : UnitsRepresentationUtils.getInstance().serializableBaseUnits()) {
            exponents =
                    ctx.mkAnd(
                            exponents,
                            ctx.mkEq(
                                    res.getExponent(baseUnit),
                                    ctx.mkAdd(
                                            lhs.getExponent(baseUnit), rhs.getExponent(baseUnit))));
        }

        // r = x * y
        // (((x=top || y=top) && r=top) ||
        // (x=bot && !y=top && r=bot) ||
        // (!x=top && y=bot && r=bot) ||
        // (!x=top && !x=bot && !y=top && !y=bot && exponents))

        BoolExpr multiplyEncoding =
                ctx.mkOr(
                        ctx.mkAnd(
                                ctx.mkOr(lhs.getUnknownUnits(), rhs.getUnknownUnits()),
                                res.getUnknownUnits()),
                        ctx.mkAnd(
                                lhs.getUnitsBottom(),
                                ctx.mkNot(rhs.getUnknownUnits()),
                                res.getUnitsBottom()),
                        ctx.mkAnd(
                                ctx.mkNot(lhs.getUnknownUnits()),
                                rhs.getUnitsBottom(),
                                res.getUnitsBottom()),
                        ctx.mkAnd(
                                ctx.mkNot(lhs.getUnknownUnits()),
                                ctx.mkNot(lhs.getUnitsBottom()),
                                ctx.mkNot(rhs.getUnknownUnits()),
                                ctx.mkNot(rhs.getUnitsBottom()),
                                ctx.mkNot(res.getUnknownUnits()),
                                ctx.mkNot(res.getUnitsBottom()),
                                exponents));
        /* @formatter:on // this is for eclipse formatter */
        return multiplyEncoding;

        // old encoding: which always computed exponents
        // res component = lhs component + rhs component
        // ctx.mkAnd(
        //        ctx.mkEq(
        //                res.getUnknownUnits(),
        //                ctx.mkOr(lhs.getUnknownUnits(), rhs.getUnknownUnits())),
        //        ctx.mkEq(
        //                res.getUnitsBottom(),
        //                ctx.mkOr(lhs.getUnitsBottom(), rhs.getUnitsBottom())),
        //        ctx.mkEq(
        //                res.getPrefixExponent(),
        //                ctx.mkAdd(lhs.getPrefixExponent(), rhs.getPrefixExponent())),
        //        exponents);
    }

    public static Z3EquationSet divide(
            Context ctx, Z3InferenceUnit lhs, Z3InferenceUnit rhs, Z3InferenceUnit res) {
        /* @formatter:off // this is for eclipse formatter */
        // Forall base units, r_exponent = lhs_exponent - rhs_exponent

        BoolExpr exponents = ctx.mkTrue();
        if (UnitsRepresentationUtils.getInstance().serializePrefix()) {
            exponents =
                    ctx.mkEq(
                            res.getPrefixExponent(),
                            ctx.mkSub(lhs.getPrefixExponent(), rhs.getPrefixExponent()));
        }
        for (String baseUnit : UnitsRepresentationUtils.getInstance().serializableBaseUnits()) {
            exponents =
                    ctx.mkAnd(
                            exponents,
                            ctx.mkEq(
                                    res.getExponent(baseUnit),
                                    ctx.mkSub(
                                            lhs.getExponent(baseUnit), rhs.getExponent(baseUnit))));
        }
        BoolExpr divideEncoding =
                ctx.mkOr(
                        ctx.mkAnd(
                                ctx.mkOr(lhs.getUnknownUnits(), rhs.getUnknownUnits()),
                                res.getUnknownUnits()),
                        ctx.mkAnd(
                                lhs.getUnitsBottom(),
                                ctx.mkNot(rhs.getUnknownUnits()),
                                res.getUnitsBottom()),
                        ctx.mkAnd(
                                ctx.mkNot(lhs.getUnknownUnits()),
                                rhs.getUnitsBottom(),
                                res.getUnitsBottom()),
                        ctx.mkAnd(
                                ctx.mkNot(lhs.getUnknownUnits()),
                                ctx.mkNot(lhs.getUnitsBottom()),
                                ctx.mkNot(rhs.getUnknownUnits()),
                                ctx.mkNot(rhs.getUnitsBottom()),
                                ctx.mkNot(res.getUnknownUnits()),
                                ctx.mkNot(res.getUnitsBottom()),
                                exponents));
        /* @formatter:on // this is for eclipse formatter */
        return divideEncoding;

        // old encoding: which always computed exponents
        // res component = lhs component - rhs component
        // ctx.mkAnd(
        //        ctx.mkEq(
        //                res.getUnknownUnits(),
        //                ctx.mkOr(lhs.getUnknownUnits(), rhs.getUnknownUnits())),
        //        ctx.mkEq(
        //                res.getUnitsBottom(),
        //                ctx.mkOr(lhs.getUnitsBottom(), rhs.getUnitsBottom())),
        //        ctx.mkEq(
        //                res.getPrefixExponent(),
        //                ctx.mkAdd(lhs.getPrefixExponent(), rhs.getPrefixExponent())),
        //        exponents);
    }
}
