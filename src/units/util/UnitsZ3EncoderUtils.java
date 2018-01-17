package units.util;

import org.checkerframework.javacutil.Pair;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import units.internalrepresentation.InferenceUnit;

/**
 * Utility class with methods for defining z3 variable names and encoding of various relationships
 * between Units.
 */
public class UnitsZ3EncoderUtils {

    private static final char idComponentSeparator = '-';
    public static final String uuSlotName = "UnknownUnits";
    public static final String ubSlotName = "UnitsBottom";
    public static final String prefixSlotName = "Prefix";

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

    // fst = snd iff the bool and int component values are equal
    // For Equality, and also Modulo
    public static BoolExpr equality(Context ctx, InferenceUnit fst, InferenceUnit snd) {
        /* @formatter:off // this is for eclipse formatter */
        BoolExpr equalityEncoding =
            ctx.mkAnd(
                ctx.mkEq(fst.getUnknownUnits(), snd.getUnknownUnits()),
                ctx.mkEq(fst.getUnitsBottom(), snd.getUnitsBottom()),
                ctx.mkEq(fst.getPrefixExponent(), snd.getPrefixExponent())
            );
        for (String baseUnit : UnitsUtils.baseUnits()) {
            equalityEncoding = ctx.mkAnd(equalityEncoding,
                ctx.mkEq(fst.getExponent(baseUnit), snd.getExponent(baseUnit))
            );
        }
        /* @formatter:on // this is for eclipse formatter */
        return equalityEncoding;
    }

    // sub <: super has 3 cases:
    // super != top and super != bottom --> sub = super or sub = bottom
    // super = top --> no constraints on sub
    // super = bottom --> sub = bottom
    public static BoolExpr subtype(Context ctx, InferenceUnit subT, InferenceUnit superT) {
        /* @formatter:off // this is for eclipse formatter */
        BoolExpr subtypeEncoding =
            ctx.mkXor(
                ctx.mkXor(
                     // super != top and super != bottom ==> sub = super or sub = bottom
                    ctx.mkAnd(
                        ctx.mkNot(superT.getUnknownUnits()),   
                        ctx.mkNot(superT.getUnitsBottom()),
                        ctx.mkXor(equality(ctx, subT, superT), superT.getUnitsBottom()) 
                    ),
                    // super = top ==> no constraints on sub
                    superT.getUnknownUnits()
                ),
                // super = bottom ==> sub = bottom
                ctx.mkAnd(superT.getUnitsBottom(), subT.getUnitsBottom())
            );
        /* @formatter:on // this is for eclipse formatter */
        return subtypeEncoding;
    }

    // For Addition and Subtraction
    public static BoolExpr tripleEquality(Context ctx, InferenceUnit lhs, InferenceUnit rhs,
            InferenceUnit res) {
        // set lhs == rhs, and rhs == res, transitively lhs == res
        return ctx.mkAnd(equality(ctx, lhs, rhs), equality(ctx, rhs, res));
    }

    public static BoolExpr multiply(Context ctx, InferenceUnit lhs, InferenceUnit rhs,
            InferenceUnit res) {
        /* @formatter:off // this is for eclipse formatter */
        // Forall base units, r_exponent = lhs_exponent + rhs_exponent
        BoolExpr exponents = ctx.mkTrue();
        for (String baseUnit : UnitsUtils.baseUnits()) {
            exponents = ctx.mkAnd(exponents,
                ctx.mkEq(
                    res.getExponent(baseUnit),
                    ctx.mkAdd(lhs.getExponent(baseUnit), rhs.getExponent(baseUnit))
                )
            );
        }
        BoolExpr multiplyEncoding =
            ctx.mkXor(
                // if either lhs or rhs is UnknownUnits or UnitsBottom, then result is UnknownUnits
                ctx.mkAnd(
                    ctx.mkOr(
                        lhs.getUnknownUnits(),
                        lhs.getUnitsBottom(),
                        rhs.getUnknownUnits(),
                        rhs.getUnitsBottom()
                    ),
                    res.getUnknownUnits()
                ),
                // otherwise res component = lhs component + rhs component
                ctx.mkAnd(
                    ctx.mkNot(res.getUnknownUnits()),
                    ctx.mkNot(res.getUnitsBottom()),
                    ctx.mkEq(
                        res.getPrefixExponent(),
                        ctx.mkAdd(lhs.getPrefixExponent(), rhs.getPrefixExponent())
                    ),
                    exponents
                )
            );
        /* @formatter:on // this is for eclipse formatter */
        return multiplyEncoding;
    }

    public static BoolExpr divide(Context ctx, InferenceUnit lhs, InferenceUnit rhs,
            InferenceUnit res) {
        /* @formatter:off // this is for eclipse formatter */
        // Forall base units, r_exponent = lhs_exponent - rhs_exponent
        BoolExpr exponents = ctx.mkTrue();
        for (String baseUnit : UnitsUtils.baseUnits()) {
            exponents = ctx.mkAnd(exponents,
                ctx.mkEq(
                    res.getExponent(baseUnit),
                    ctx.mkSub(lhs.getExponent(baseUnit), rhs.getExponent(baseUnit))
                )
            );
        }
        BoolExpr divideEncoding =
            ctx.mkXor(
                // if either lhs or rhs is UnknownUnits or UnitsBottom, then result is UnknownUnits
                ctx.mkAnd(
                    ctx.mkOr(
                        lhs.getUnknownUnits(),
                        lhs.getUnitsBottom(),
                        rhs.getUnknownUnits(),
                        rhs.getUnitsBottom()
                    ),
                    res.getUnknownUnits()
                ),
                // otherwise res component = lhs component - rhs component
                ctx.mkAnd(
                    ctx.mkNot(res.getUnknownUnits()),
                    ctx.mkNot(res.getUnitsBottom()),
                    ctx.mkEq(
                        res.getPrefixExponent(),
                        ctx.mkSub(lhs.getPrefixExponent(), rhs.getPrefixExponent())
                    ),
                    exponents
                )
            );
        /* @formatter:on // this is for eclipse formatter */
        return divideEncoding;
    }
}
