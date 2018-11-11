package units.solvers.backend.gje.encoder;

import backend.gje.GJEFormatTranslator;
import backend.gje.encoder.GJEAbstractConstraintEncoder;
import checkers.inference.model.ArithmeticConstraint.ArithmeticOperationKind;
import checkers.inference.model.ArithmeticVariableSlot;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.ArithmeticConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import java.util.Map;
import java.util.Set;
import org.checkerframework.javacutil.BugInCF;
import units.representation.TypecheckUnit;
import units.solvers.backend.gje.representation.GJEInferenceUnit;

public class UnitsGJEArithmeticConstraintEncoder
        extends GJEAbstractConstraintEncoder<GJEInferenceUnit, TypecheckUnit>
        implements ArithmeticConstraintEncoder<Map<String, Set<String>>> {

    public UnitsGJEArithmeticConstraintEncoder(
            Lattice lattice,
            GJEFormatTranslator<GJEInferenceUnit, TypecheckUnit> gjeFormatTranslator) {
        super(lattice, gjeFormatTranslator);
    }

    // Encoding for var-var, var-const, const-var combos of add/sub, and also const-const for
    // mul/div/mod
    protected Map<String, Set<String>> encode(
            ArithmeticOperationKind operation,
            Slot leftOperand,
            Slot rightOperand,
            ArithmeticVariableSlot result) {
        switch (operation) {
            case PLUS:
            case MINUS:
                // Addition or Subtraction between 2 slots resulting in result slot, is encoded as a
                // pair of subtype constraints
                GJEInferenceUnit left = leftOperand.serialize(gjeFormatTranslator);
                GJEInferenceUnit right = rightOperand.serialize(gjeFormatTranslator);
                GJEInferenceUnit res = result.serialize(gjeFormatTranslator);

                return UnitsGJEEncoderUtils.tripleEquality(left, right, res);
            case MULTIPLY:
                // Multiplication between 2 slots resulting in result slot, is the sum of the
                // component exponents unless either leftOperand or rightOperand is UnknownUnits or
                // UnitsBottom, for which then the result is always UnknownUnits
                return null;
                //                return UnitsZ3SmtEncoderUtils.multiply(
                //                        ctx,
                //                        leftOperand.serialize(gjeFormatTranslator),
                //                        rightOperand.serialize(gjeFormatTranslator),
                //                        result.serialize(gjeFormatTranslator));
            case DIVIDE:
                // Division between 2 slots resulting in result slot, is the difference of the
                // component exponents unless either leftOperand or rightOperand is UnknownUnits or
                // UnitsBottom, for which then the result is always UnknownUnits
                return null;
                //                return UnitsZ3SmtEncoderUtils.divide(
                //                        ctx,
                //                        leftOperand.serialize(gjeFormatTranslator),
                //                        rightOperand.serialize(gjeFormatTranslator),
                //                        result.serialize(gjeFormatTranslator));
            case REMAINDER:
                // Modulus between 2 slots resulting in result slot, is always an equality between
                // leftOperand and result slots
                return null;
                //                return UnitsZ3SmtEncoderUtils.equality(
                //                        ctx,
                //                        leftOperand.serialize(gjeFormatTranslator),
                //                        result.serialize(gjeFormatTranslator));
            default:
                throw new BugInCF(
                        "Attempting to encode an unsupported arithmetic operation: "
                                + operation
                                + " leftOperand: "
                                + leftOperand
                                + " rightOperand: "
                                + rightOperand
                                + " result: "
                                + result);
        }
    }

    @Override
    public Map<String, Set<String>> encodeVariable_Variable(
            ArithmeticOperationKind operation,
            VariableSlot leftOperand,
            VariableSlot rightOperand,
            ArithmeticVariableSlot result) {
        return encode(operation, leftOperand, rightOperand, result);
    }

    @Override
    public Map<String, Set<String>> encodeVariable_Constant(
            ArithmeticOperationKind operation,
            VariableSlot leftOperand,
            ConstantSlot rightOperand,
            ArithmeticVariableSlot result) {
        return encode(operation, leftOperand, rightOperand, result);
    }

    @Override
    public Map<String, Set<String>> encodeConstant_Variable(
            ArithmeticOperationKind operation,
            ConstantSlot leftOperand,
            VariableSlot rightOperand,
            ArithmeticVariableSlot result) {
        return encode(operation, leftOperand, rightOperand, result);
    }

    @Override
    public Map<String, Set<String>> encodeConstant_Constant(
            ArithmeticOperationKind operation,
            ConstantSlot leftOperand,
            ConstantSlot rightOperand,
            ArithmeticVariableSlot result) {
        switch (operation) {
            case PLUS:
            case MINUS:
                return null;

                // if leftOperand == rightOperand, then encode equality between rightOperand and
                // result
                //                return UnitsTypecheckUtils.unitsEqual(
                //                                leftOperand.getValue(), rightOperand.getValue())
                //                        ? UnitsZ3SmtEncoderUtils.equality(
                //                                ctx,
                //                                rightOperand.serialize(gjeFormatTranslator),
                //                                result.serialize(gjeFormatTranslator))
                //                        : contradictoryValue;
            case MULTIPLY:
                // It is more efficient to encode an equality between the result of leftOperand *
                // rightOperand and result, but to do that requires access to slotManager here to
                // create a constant slot for the annotation mirror of the result of leftOperand *
                // rightOperand. We defer, regrettably, to use z3 to do the calculations instead.
                return encode(operation, leftOperand, rightOperand, result);
            case DIVIDE:
                // It is more efficient to encode an equality between the result of leftOperand /
                // rightOperand and result, but to do that requires access to slotManager here to
                // create a constant slot for the annotation mirror of the result of leftOperand /
                // rightOperand. We defer, regrettably, to use z3 to do the calculations instead.
                return encode(operation, leftOperand, rightOperand, result);
            case REMAINDER:
                return encode(operation, leftOperand, rightOperand, result);
            default:
                throw new BugInCF(
                        "Attempting to encode an unsupported arithmetic operation: "
                                + operation
                                + " leftOperand: "
                                + leftOperand
                                + " rightOperand: "
                                + rightOperand
                                + " result: "
                                + result);
        }
    }
}
