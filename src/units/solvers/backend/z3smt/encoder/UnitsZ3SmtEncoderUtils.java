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

    // for syntax friendliness
    private static UnitsRepresentationUtils unitsRepUtils() {
        return UnitsRepresentationUtils.getInstance();
    }

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

    private static BoolExpr wellformedBaseUnit(
            Context ctx, Z3InferenceUnit unit, BoolExpr allExponentsAreZero) {
        return mkOneHot(
                ctx,
                ctx.mkAnd(ctx.mkNot(unit.getUnknownUnits()), ctx.mkNot(unit.getUnitsBottom())),
                ctx.mkAnd(unit.getUnknownUnits(), allExponentsAreZero),
                ctx.mkAnd(unit.getUnitsBottom(), allExponentsAreZero));
    }

    /** Slot well-formedness constraint: that either uu = true, ub = true, or uu == ub = false */
    public static Z3EquationSet slotWellformedness(Context ctx, Z3InferenceUnit unit) {
        // for GJE experiment
        // return ctx.mkAnd(ctx.mkNot(unit.getUnknownUnits()),
        // ctx.mkNot(unit.getUnitsBottom()));

        Z3EquationSet result = new Z3EquationSet();

        // option 1: simpler
        // BoolExpr wf = ctx.mkNot(ctx.mkAnd(unit.getUnknownUnits(),
        // unit.getUnitsBottom()));
        //
        // if (unitsRepUtils().serializeOnlyTopAndBot()) {
        // result.addEquation(Z3EquationSet.topAndBottomKey, wf);
        // }
        //
        // if (unitsRepUtils().serializePrefix()) {
        // result.addEquation(Z3EquationSet.prefixExponentKey, wf);
        // }
        //
        // for (String baseUnit : unitsRepUtils().serializableBaseUnits()) {
        // result.addEquation(baseUnit, wf);
        // }

        // option 2: exponents also zero
        IntNum zero = ctx.mkInt(0);

        // BoolExpr wf = ctx.mkNot(ctx.mkAnd(unit.getUnknownUnits(),
        // unit.getUnitsBottom()));

        if (unitsRepUtils().serializeOnlyTopAndBot()) {
            result.addEquation(
                    Z3EquationSet.topAndBottomKey, wellformedBaseUnit(ctx, unit, ctx.mkTrue()));
            // ctx.mkNot(ctx.mkAnd(unit.getUnknownUnits(), unit.getUnitsBottom())));
        }

        if (unitsRepUtils().serializePrefix()) {
            result.addEquation(
                    Z3EquationSet.prefixExponentKey,
                    wellformedBaseUnit(ctx, unit, ctx.mkEq(unit.getPrefixExponent(), zero)));
        }

        for (String baseUnit : unitsRepUtils().serializableBaseUnits()) {
            result.addEquation(
                    baseUnit,
                    wellformedBaseUnit(ctx, unit, ctx.mkEq(unit.getExponent(baseUnit), zero)));
        }

        return result;

        // truthtable xor (xor ((not x and not y), x), y)
        // TODO: more preferable to not have to encode exponent == 0 in
        // wellformedness, but currently we must do so in order to have exponent
        // variable declarations outputted for the z3 files
        //        BoolExpr allExponentsAreZero = allExponentsAreZero(ctx, unit);
        //        /* @formatter:off // this is for eclipse formatter */
        //        return UnitsZ3SmtEncoderUtils.mkOneHot(
        //                ctx,
        //                ctx.mkAnd(ctx.mkNot(unit.getUnknownUnits()), ctx.mkNot(unit.getUnitsBottom())),
        //                ctx.mkAnd(unit.getUnknownUnits(), allExponentsAreZero),
        //                ctx.mkAnd(unit.getUnitsBottom(), allExponentsAreZero));
        /* @formatter:on // this is for eclipse formatter */

        // simplify xor (xor ((not x and not y), x), y)
        // // Simplified version:
        // return ctx.mkNot(ctx.mkAnd(unit.getUnknownUnits(), unit.getUnitsBottom()));
        // return ctx.mkOr(ctx.mkNot(unit.getUnknownUnits()), ctx.mkNot(unit.getUnitsBottom()));
    }

    /** Slot preference constraint: that the slot != top && slot != bot */
    public static Z3EquationSet slotNotTopBotPreference(Context ctx, Z3InferenceUnit unit) {
        Z3EquationSet result = new Z3EquationSet();

        BoolExpr notTopAndNotBot =
                ctx.mkAnd(ctx.mkNot(unit.getUnknownUnits()), ctx.mkNot(unit.getUnitsBottom()));
        IntNum zero = ctx.mkInt(0);

        if (unitsRepUtils().serializeOnlyTopAndBot()) {
            result.addEquation(Z3EquationSet.topAndBottomKey, notTopAndNotBot);
        }

        if (unitsRepUtils().serializePrefix()) {
            result.addEquation(Z3EquationSet.prefixExponentKey, notTopAndNotBot);
        }

        for (String baseUnit : unitsRepUtils().serializableBaseUnits()) {
            result.addEquation(baseUnit, notTopAndNotBot);
        }

        return result;
    }

    /** Slot preference constraint: that the slot == dimensionless */
    public static Z3EquationSet slotIsDimensionlessPreference(Context ctx, Z3InferenceUnit unit) {
        Z3EquationSet result = new Z3EquationSet();

        BoolExpr notTopAndNotBot =
                ctx.mkAnd(ctx.mkNot(unit.getUnknownUnits()), ctx.mkNot(unit.getUnitsBottom()));
        IntNum zero = ctx.mkInt(0);

        if (unitsRepUtils().serializeOnlyTopAndBot()) {
            result.addEquation(Z3EquationSet.topAndBottomKey, notTopAndNotBot);
        }

        if (unitsRepUtils().serializePrefix()) {
            BoolExpr prefixIsZero = ctx.mkEq(unit.getPrefixExponent(), zero);
            result.addEquation(
                    Z3EquationSet.prefixExponentKey, ctx.mkAnd(notTopAndNotBot, prefixIsZero));
        }

        for (String baseUnit : unitsRepUtils().serializableBaseUnits()) {
            BoolExpr baseUnitIsZero = ctx.mkEq(unit.getExponent(baseUnit), zero);
            result.addEquation(baseUnit, ctx.mkAnd(notTopAndNotBot, baseUnitIsZero));
        }

        return result;
    }

    // =========================================================================================

    // fst = snd iff the bool and int component values are equal
    // For Equality, and also Modulo
    public static Z3EquationSet equality(Context ctx, Z3InferenceUnit fst, Z3InferenceUnit snd) {
        Z3EquationSet result = new Z3EquationSet();

        BoolExpr topsAndBottoms =
                ctx.mkAnd(
                        ctx.mkEq(fst.getUnknownUnits(), snd.getUnknownUnits()),
                        ctx.mkEq(fst.getUnitsBottom(), snd.getUnitsBottom()));

        // this needs to be generated if we don't serialize prefix or any units,
        // otherwise omit as it is solved as part of all number planes (in prefix or a
        // base unit)
        if (unitsRepUtils().serializeOnlyTopAndBot()) {
            result.addEquation(Z3EquationSet.topAndBottomKey, topsAndBottoms);
        }

        if (unitsRepUtils().serializePrefix()) {
            result.addEquation(
                    Z3EquationSet.prefixExponentKey,
                    ctx.mkAnd(
                            topsAndBottoms,
                            ctx.mkEq(fst.getPrefixExponent(), snd.getPrefixExponent())));
        }

        for (String baseUnit : unitsRepUtils().serializableBaseUnits()) {
            result.addEquation(
                    baseUnit,
                    ctx.mkAnd(
                            topsAndBottoms,
                            ctx.mkEq(fst.getExponent(baseUnit), snd.getExponent(baseUnit))));
        }

        return result;
    }

    private static BoolExpr subtype(
            Context ctx, Z3InferenceUnit subT, Z3InferenceUnit superT, BoolExpr equality) {

        /* @formatter:off // this is for eclipse formatter */
        return ctx.mkOr(
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
                        equality));
        /* @formatter:on // this is for eclipse formatter */
    }

    // sub <: super has 6 cases:
    // bot <: bot
    // bot <: x
    // bot <: top
    // x <: top
    // top <: top
    // x <: x
    public static Z3EquationSet subtype(Context ctx, Z3InferenceUnit subT, Z3InferenceUnit superT) {
        Z3EquationSet result = new Z3EquationSet();

        Z3EquationSet equality = equality(ctx, subT, superT);

        if (unitsRepUtils().serializeOnlyTopAndBot()) {
            result.addEquation(
                    Z3EquationSet.topAndBottomKey,
                    subtype(
                            ctx,
                            subT,
                            superT,
                            equality.getEquation(Z3EquationSet.topAndBottomKey)));
        }

        if (unitsRepUtils().serializePrefix()) {
            result.addEquation(
                    Z3EquationSet.prefixExponentKey,
                    subtype(
                            ctx,
                            subT,
                            superT,
                            equality.getEquation(Z3EquationSet.prefixExponentKey)));
        }

        for (String baseUnit : unitsRepUtils().serializableBaseUnits()) {
            result.addEquation(
                    baseUnit, subtype(ctx, subT, superT, equality.getEquation(baseUnit)));
        }

        return result;

        //        /* @formatter:off // this is for eclipse formatter */
        //        BoolExpr subtypeEncoding =
        //                ctx.mkOr(
        //                        // sub = bot
        //                        subT.getUnitsBottom(),
        //                        // super = top
        //                        superT.getUnknownUnits(),
        //                        // if neither is top or bottom then they must be equal: sub = super
        //                        ctx.mkAnd(
        //                                ctx.mkNot(subT.getUnknownUnits()),
        //                                ctx.mkNot(subT.getUnitsBottom()),
        //                                ctx.mkNot(superT.getUnknownUnits()),
        //                                ctx.mkNot(superT.getUnitsBottom()),
        //                                equality(ctx, subT, superT)));
        //        /* @formatter:on // this is for eclipse formatter */
        //        return subtypeEncoding;

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

        Z3EquationSet result = new Z3EquationSet();

        Z3EquationSet equalityLR = equality(ctx, lhs, rhs);

        Z3EquationSet equalityRS = equality(ctx, rhs, res);

        if (unitsRepUtils().serializeOnlyTopAndBot()) {
            result.addEquation(
                    Z3EquationSet.topAndBottomKey,
                    ctx.mkAnd(
                            equalityLR.getEquation(Z3EquationSet.topAndBottomKey),
                            equalityRS.getEquation(Z3EquationSet.topAndBottomKey)));
        }

        if (unitsRepUtils().serializePrefix()) {
            result.addEquation(
                    Z3EquationSet.prefixExponentKey,
                    ctx.mkAnd(
                            equalityLR.getEquation(Z3EquationSet.prefixExponentKey),
                            equalityRS.getEquation(Z3EquationSet.prefixExponentKey)));
        }

        for (String baseUnit : unitsRepUtils().serializableBaseUnits()) {
            result.addEquation(
                    baseUnit,
                    ctx.mkAnd(equalityLR.getEquation(baseUnit), equalityRS.getEquation(baseUnit)));
        }

        return result;
        // return ctx.mkAnd(equality(ctx, lhs, rhs), equality(ctx, rhs, res));
    }

    public static Z3EquationSet comparable(Context ctx, Z3InferenceUnit fst, Z3InferenceUnit snd) {

        // fst <: snd or snd <: fst

        Z3EquationSet result = new Z3EquationSet();

        Z3EquationSet subtypeFS = subtype(ctx, fst, snd);

        Z3EquationSet subtypeSF = subtype(ctx, snd, fst);

        if (unitsRepUtils().serializeOnlyTopAndBot()) {
            result.addEquation(
                    Z3EquationSet.topAndBottomKey,
                    ctx.mkOr(
                            subtypeFS.getEquation(Z3EquationSet.topAndBottomKey),
                            subtypeSF.getEquation(Z3EquationSet.topAndBottomKey)));
        }

        if (unitsRepUtils().serializePrefix()) {
            result.addEquation(
                    Z3EquationSet.prefixExponentKey,
                    ctx.mkOr(
                            subtypeFS.getEquation(Z3EquationSet.prefixExponentKey),
                            subtypeSF.getEquation(Z3EquationSet.prefixExponentKey)));
        }

        for (String baseUnit : unitsRepUtils().serializableBaseUnits()) {
            result.addEquation(
                    baseUnit,
                    ctx.mkOr(subtypeFS.getEquation(baseUnit), subtypeSF.getEquation(baseUnit)));
        }

        return result;

        // return ctx.mkOr(
        // UnitsZ3SmtEncoderUtils.subtype(ctx, fst, snd),
        // UnitsZ3SmtEncoderUtils.subtype(ctx, snd, fst));
    }

    public static Z3EquationSet additionSubtraction(
            Context ctx, Z3InferenceUnit lhs, Z3InferenceUnit rhs, Z3InferenceUnit res) {

        Z3EquationSet result = new Z3EquationSet();

        Z3EquationSet subtypeLRe = subtype(ctx, lhs, res);

        Z3EquationSet subtypeRRe = subtype(ctx, rhs, res);

        if (unitsRepUtils().serializeOnlyTopAndBot()) {
            result.addEquation(
                    Z3EquationSet.topAndBottomKey,
                    ctx.mkAnd(
                            subtypeLRe.getEquation(Z3EquationSet.topAndBottomKey),
                            subtypeRRe.getEquation(Z3EquationSet.topAndBottomKey)));
        }

        if (unitsRepUtils().serializePrefix()) {
            result.addEquation(
                    Z3EquationSet.prefixExponentKey,
                    ctx.mkAnd(
                            subtypeLRe.getEquation(Z3EquationSet.prefixExponentKey),
                            subtypeRRe.getEquation(Z3EquationSet.prefixExponentKey)));
        }

        for (String baseUnit : unitsRepUtils().serializableBaseUnits()) {
            result.addEquation(
                    baseUnit,
                    ctx.mkAnd(subtypeLRe.getEquation(baseUnit), subtypeRRe.getEquation(baseUnit)));
        }

        return result;

        // return ctx.mkAnd(
        // UnitsZ3SmtEncoderUtils.subtype(ctx, lhs, res),
        // UnitsZ3SmtEncoderUtils.subtype(ctx, rhs, res));

        // // 3 way equality (ie leftOperand == rightOperand, and rightOperand == result).
        // return UnitsZ3SmtEncoderUtils.tripleEquality(ctx,
        // leftOperand.serialize(z3SmtFormatTranslator),
        // rightOperand.serialize(z3SmtFormatTranslator),
        // result.serialize(z3SmtFormatTranslator));
    }

    private static BoolExpr multiplyDivideTopAndBottom(
            Context ctx,
            Z3InferenceUnit lhs,
            Z3InferenceUnit rhs,
            Z3InferenceUnit res,
            BoolExpr exponents) {
        // r = x * y
        // (((x=top || y=top) && r=top) ||
        // (x=bot && !y=top && r=bot) ||
        // (!x=top && y=bot && r=bot) ||
        // (!x=top && !x=bot && !y=top && !y=bot && exponents))

        /* @formatter:off // this is for eclipse formatter */
        return ctx.mkOr(
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
    }

    public static Z3EquationSet multiply(
            Context ctx, Z3InferenceUnit lhs, Z3InferenceUnit rhs, Z3InferenceUnit res) {

        Z3EquationSet result = new Z3EquationSet();

        if (unitsRepUtils().serializeOnlyTopAndBot()) {
            result.addEquation(
                    Z3EquationSet.topAndBottomKey,
                    multiplyDivideTopAndBottom(ctx, lhs, rhs, res, ctx.mkTrue()));
        }

        // Forall base units, r_exponent = lhs_exponent + rhs_exponent
        if (unitsRepUtils().serializePrefix()) {
            result.addEquation(
                    Z3EquationSet.prefixExponentKey,
                    multiplyDivideTopAndBottom(
                            ctx,
                            lhs,
                            rhs,
                            res,
                            ctx.mkEq(
                                    res.getPrefixExponent(),
                                    ctx.mkAdd(lhs.getPrefixExponent(), rhs.getPrefixExponent()))));
        }

        for (String baseUnit : unitsRepUtils().serializableBaseUnits()) {
            result.addEquation(
                    baseUnit,
                    multiplyDivideTopAndBottom(
                            ctx,
                            lhs,
                            rhs,
                            res,
                            ctx.mkEq(
                                    res.getExponent(baseUnit),
                                    ctx.mkAdd(
                                            lhs.getExponent(baseUnit),
                                            rhs.getExponent(baseUnit)))));
        }

        return result;
        //
        //
        //        BoolExpr multiplyEncoding =
        //                ctx.mkOr(
        //                        ctx.mkAnd(
        //                                ctx.mkOr(lhs.getUnknownUnits(), rhs.getUnknownUnits()),
        //                                res.getUnknownUnits()),
        //                        ctx.mkAnd(
        //                                lhs.getUnitsBottom(),
        //                                ctx.mkNot(rhs.getUnknownUnits()),
        //                                res.getUnitsBottom()),
        //                        ctx.mkAnd(
        //                                ctx.mkNot(lhs.getUnknownUnits()),
        //                                rhs.getUnitsBottom(),
        //                                res.getUnitsBottom()),
        //                        ctx.mkAnd(
        //                                ctx.mkNot(lhs.getUnknownUnits()),
        //                                ctx.mkNot(lhs.getUnitsBottom()),
        //                                ctx.mkNot(rhs.getUnknownUnits()),
        //                                ctx.mkNot(rhs.getUnitsBottom()),
        //                                ctx.mkNot(res.getUnknownUnits()),
        //                                ctx.mkNot(res.getUnitsBottom()),
        //                                exponents));
        //
        //        return multiplyEncoding;

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
        Z3EquationSet result = new Z3EquationSet();

        if (unitsRepUtils().serializeOnlyTopAndBot()) {
            result.addEquation(
                    Z3EquationSet.topAndBottomKey,
                    multiplyDivideTopAndBottom(ctx, lhs, rhs, res, ctx.mkTrue()));
        }

        // Forall base units, r_exponent = lhs_exponent + rhs_exponent
        if (unitsRepUtils().serializePrefix()) {
            result.addEquation(
                    Z3EquationSet.prefixExponentKey,
                    multiplyDivideTopAndBottom(
                            ctx,
                            lhs,
                            rhs,
                            res,
                            ctx.mkEq(
                                    res.getPrefixExponent(),
                                    ctx.mkSub(lhs.getPrefixExponent(), rhs.getPrefixExponent()))));
        }

        for (String baseUnit : unitsRepUtils().serializableBaseUnits()) {
            result.addEquation(
                    baseUnit,
                    multiplyDivideTopAndBottom(
                            ctx,
                            lhs,
                            rhs,
                            res,
                            ctx.mkEq(
                                    res.getExponent(baseUnit),
                                    ctx.mkSub(
                                            lhs.getExponent(baseUnit),
                                            rhs.getExponent(baseUnit)))));
        }

        return result;

        //        /* @formatter:off // this is for eclipse formatter */
        //        // Forall base units, r_exponent = lhs_exponent - rhs_exponent
        //
        //        BoolExpr exponents = ctx.mkTrue();
        //        if (unitsRepUtils().serializePrefix()) {
        //            exponents =
        //                    ctx.mkEq(
        //                            res.getPrefixExponent(),
        //                            ctx.mkSub(lhs.getPrefixExponent(), rhs.getPrefixExponent()));
        //        }
        //        for (String baseUnit : unitsRepUtils().serializableBaseUnits()) {
        //            exponents =
        //                    ctx.mkAnd(
        //                            exponents,
        //                            ctx.mkEq(
        //                                    res.getExponent(baseUnit),
        //                                    ctx.mkSub(
        //                                            lhs.getExponent(baseUnit), rhs.getExponent(baseUnit))));
        //        }
        //        BoolExpr divideEncoding =
        //                ctx.mkOr(
        //                        ctx.mkAnd(
        //                                ctx.mkOr(lhs.getUnknownUnits(), rhs.getUnknownUnits()),
        //                                res.getUnknownUnits()),
        //                        ctx.mkAnd(
        //                                lhs.getUnitsBottom(),
        //                                ctx.mkNot(rhs.getUnknownUnits()),
        //                                res.getUnitsBottom()),
        //                        ctx.mkAnd(
        //                                ctx.mkNot(lhs.getUnknownUnits()),
        //                                rhs.getUnitsBottom(),
        //                                res.getUnitsBottom()),
        //                        ctx.mkAnd(
        //                                ctx.mkNot(lhs.getUnknownUnits()),
        //                                ctx.mkNot(lhs.getUnitsBottom()),
        //                                ctx.mkNot(rhs.getUnknownUnits()),
        //                                ctx.mkNot(rhs.getUnitsBottom()),
        //                                ctx.mkNot(res.getUnknownUnits()),
        //                                ctx.mkNot(res.getUnitsBottom()),
        //                                exponents));
        //        /* @formatter:on // this is for eclipse formatter */
        //        return divideEncoding;

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
