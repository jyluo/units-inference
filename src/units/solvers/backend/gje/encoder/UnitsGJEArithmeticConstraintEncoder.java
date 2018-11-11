package units.solvers.backend.gje.encoder;

import checkers.inference.model.ArithmeticConstraint.ArithmeticOperationKind;
import checkers.inference.model.ArithmeticVariableSlot;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.ArithmeticConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import org.checkerframework.javacutil.BugInCF;
import units.solvers.backend.gje.UnitsGJEFormatTranslator;
import units.solvers.backend.gje.representation.GJEEquationSet;
import units.solvers.backend.gje.representation.GJEInferenceUnit;
import units.util.UnitsTypecheckUtils;

public class UnitsGJEArithmeticConstraintEncoder extends UnitsGJEAbstractConstraintEncoder
        implements ArithmeticConstraintEncoder<GJEEquationSet> {

    public UnitsGJEArithmeticConstraintEncoder(
            Lattice lattice, UnitsGJEFormatTranslator formatTranslator) {
        super(lattice, formatTranslator);
    }

    // Encoding for var-var, var-const, const-var combos of add/sub, and also
    // const-const for mul/div/mod
    protected GJEEquationSet encode(
            ArithmeticOperationKind operation,
            Slot leftOperand,
            Slot rightOperand,
            ArithmeticVariableSlot result) {
        switch (operation) {
            case PLUS:
            case MINUS:
                // Addition or Subtraction between 2 slots resulting in result slot
                GJEInferenceUnit left = leftOperand.serialize(formatTranslator);
                GJEInferenceUnit right = rightOperand.serialize(formatTranslator);
                GJEInferenceUnit res = result.serialize(formatTranslator);

                return UnitsGJEEncoderUtils.tripleEquality(left, right, res);
            case MULTIPLY:
                // Multiplication between 2 slots resulting in result slot
                return null;
                // return UnitsGJEEncoderUtils.multiply(
                // leftOperand.serialize(gjeFormatTranslator),
                // rightOperand.serialize(gjeFormatTranslator),
                // result.serialize(gjeFormatTranslator));
            case DIVIDE:
                // Division between 2 slots resulting in result slot
                return null;
                // return UnitsGJEEncoderUtils.divide(
                // leftOperand.serialize(gjeFormatTranslator),
                // rightOperand.serialize(gjeFormatTranslator),
                // result.serialize(gjeFormatTranslator));
            case REMAINDER:
                // Modulus between 2 slots resulting in result slot, is always
                // an equality between leftOperand and result slots
                return UnitsGJEEncoderUtils.equality(
                        leftOperand.serialize(formatTranslator),
                        result.serialize(formatTranslator));
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
    public GJEEquationSet encodeVariable_Variable(
            ArithmeticOperationKind operation,
            VariableSlot leftOperand,
            VariableSlot rightOperand,
            ArithmeticVariableSlot result) {
        return encode(operation, leftOperand, rightOperand, result);
    }

    @Override
    public GJEEquationSet encodeVariable_Constant(
            ArithmeticOperationKind operation,
            VariableSlot leftOperand,
            ConstantSlot rightOperand,
            ArithmeticVariableSlot result) {
        return encode(operation, leftOperand, rightOperand, result);
    }

    @Override
    public GJEEquationSet encodeConstant_Variable(
            ArithmeticOperationKind operation,
            ConstantSlot leftOperand,
            VariableSlot rightOperand,
            ArithmeticVariableSlot result) {
        return encode(operation, leftOperand, rightOperand, result);
    }

    @Override
    public GJEEquationSet encodeConstant_Constant(
            ArithmeticOperationKind operation,
            ConstantSlot leftOperand,
            ConstantSlot rightOperand,
            ArithmeticVariableSlot result) {
        switch (operation) {
            case PLUS:
            case MINUS:
                // if leftOperand == rightOperand, then encode equality between
                // rightOperand and result
                return UnitsTypecheckUtils.unitsEqual(
                                leftOperand.getValue(), rightOperand.getValue())
                        ? UnitsGJEEncoderUtils.equality(
                                rightOperand.serialize(formatTranslator),
                                result.serialize(formatTranslator))
                        : contradictoryValue;
            case MULTIPLY:
                // It is more efficient to encode an equality between the result
                // of leftOperand * rightOperand and result, but to do that
                // requires access to slotManager here to create a constant slot
                // for the annotation mirror of the result of leftOperand *
                // rightOperand. We defer, regrettably, to use the solver to do
                // the calculations instead.
                return encode(operation, leftOperand, rightOperand, result);
            case DIVIDE:
                // It is more efficient to encode an equality between the result
                // of leftOperand / rightOperand and result, but to do that
                // requires access to slotManager here to create a constant slot
                // for the annotation mirror of the result of leftOperand /
                // rightOperand. We defer, regrettably, to use the solver to do
                // the calculations instead.
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
