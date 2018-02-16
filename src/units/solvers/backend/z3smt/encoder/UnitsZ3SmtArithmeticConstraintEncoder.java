package units.solvers.backend.z3smt.encoder;

import org.checkerframework.javacutil.ErrorReporter;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import backend.z3smt.Z3SmtFormatTranslator;
import backend.z3smt.encoder.Z3SmtAbstractConstraintEncoder;
import checkers.inference.model.ArithmeticConstraint.ArithmeticOperationKind;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.ArithmeticConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import units.internalrepresentation.InferenceUnit;
import units.internalrepresentation.TypecheckUnit;
import units.util.UnitsTypecheckUtils;
import units.util.UnitsZ3SmtEncoderUtils;

public class UnitsZ3SmtArithmeticConstraintEncoder
        extends Z3SmtAbstractConstraintEncoder<InferenceUnit, TypecheckUnit>
        implements ArithmeticConstraintEncoder<BoolExpr> {

    public UnitsZ3SmtArithmeticConstraintEncoder(Lattice lattice, Context ctx,
            Z3SmtFormatTranslator<InferenceUnit, TypecheckUnit> z3IntFormatTranslator) {
        super(lattice, ctx, z3IntFormatTranslator);
    }

    // Encoding for var-var, var-const, const-var combos of add/sub, and also const-const for
    // mul/div/mod
    protected BoolExpr encode(ArithmeticOperationKind operation, Slot leftOperand,
            Slot rightOperand, Slot result) {
        switch (operation) {
            case ADDITION:
            case SUBTRACTION:
                // Addition or Subtraction between 2 slots resulting in result slot, is encoded as a
                // 3 way equality (ie leftOperand == rightOperand, and rightOperand == result).
                return UnitsZ3SmtEncoderUtils.tripleEquality(ctx,
                        leftOperand.serialize(z3SmtFormatTranslator),
                        rightOperand.serialize(z3SmtFormatTranslator),
                        result.serialize(z3SmtFormatTranslator));
            case MULTIPLICATION:
                // Multiplication between 2 slots resulting in result slot, is the sum of the
                // component exponents unless either leftOperand or rightOperand is UnknownUnits or
                // UnitsBottom, for which then the result is always UnknownUnits
                return UnitsZ3SmtEncoderUtils.multiply(ctx,
                        leftOperand.serialize(z3SmtFormatTranslator),
                        rightOperand.serialize(z3SmtFormatTranslator),
                        result.serialize(z3SmtFormatTranslator));
            case DIVISION:
                // Division between 2 slots resulting in result slot, is the difference of the
                // component exponents unless either leftOperand or rightOperand is UnknownUnits or
                // UnitsBottom, for which then the result is always UnknownUnits
                return UnitsZ3SmtEncoderUtils.divide(ctx,
                        leftOperand.serialize(z3SmtFormatTranslator),
                        rightOperand.serialize(z3SmtFormatTranslator),
                        result.serialize(z3SmtFormatTranslator));
            case MODULUS:
                // Modulus between 2 slots resulting in result slot, is always an equality between
                // leftOperand and result slots
                return UnitsZ3SmtEncoderUtils.equality(ctx,
                        leftOperand.serialize(z3SmtFormatTranslator),
                        result.serialize(z3SmtFormatTranslator));
            default:
                ErrorReporter
                        .errorAbort("Attempting to encode an unsupported arithmetic operation: "
                                + operation + " leftOperand: " + leftOperand + " rightOperand: "
                                + rightOperand + " result: " + result);
                return null;
        }
    }

    @Override
    public BoolExpr encodeVariable_Variable(ArithmeticOperationKind operation,
            VariableSlot leftOperand, VariableSlot rightOperand, VariableSlot result) {
        return encode(operation, leftOperand, rightOperand, result);
    }

    @Override
    public BoolExpr encodeVariable_Constant(ArithmeticOperationKind operation,
            VariableSlot leftOperand, ConstantSlot rightOperand, VariableSlot result) {
        return encode(operation, leftOperand, rightOperand, result);
    }

    @Override
    public BoolExpr encodeConstant_Variable(ArithmeticOperationKind operation,
            ConstantSlot leftOperand, VariableSlot rightOperand, VariableSlot result) {
        return encode(operation, leftOperand, rightOperand, result);
    }

    @Override
    public BoolExpr encodeConstant_Constant(ArithmeticOperationKind operation,
            ConstantSlot leftOperand, ConstantSlot rightOperand, VariableSlot result) {
        switch (operation) {
            case ADDITION:
            case SUBTRACTION:
                // TODO: do constant constant checks inside encode() ?

                // if leftOperand == rightOperand, then encode equality between rightOperand and
                // result
                return UnitsTypecheckUtils.unitsEqual(leftOperand.getValue(),
                        rightOperand.getValue())
                                ? UnitsZ3SmtEncoderUtils.equality(ctx,
                                        rightOperand.serialize(z3SmtFormatTranslator),
                                        result.serialize(z3SmtFormatTranslator))
                                : contradictoryValue;
            case MULTIPLICATION:
                // It is more efficient to encode an equality between the result of leftOperand *
                // rightOperand and result, but to do that requires access to slotManager here to
                // create a constant slot for the annotation mirror of the result of leftOperand *
                // rightOperand. We defer, regrettably, to use z3 to do the calculations instead.
                return encode(operation, leftOperand, rightOperand, result);
            case DIVISION:
                // It is more efficient to encode an equality between the result of leftOperand /
                // rightOperand and result, but to do that requires access to slotManager here to
                // create a constant slot for the annotation mirror of the result of leftOperand /
                // rightOperand. We defer, regrettably, to use z3 to do the calculations instead.
                return encode(operation, leftOperand, rightOperand, result);
            case MODULUS:
                return encode(operation, leftOperand, rightOperand, result);
            default:
                ErrorReporter
                        .errorAbort("Attempting to encode an unsupported arithmetic operation: "
                                + operation + " leftOperand: " + leftOperand + " rightOperand: "
                                + rightOperand + " result: " + result);
                return null;
        }
    }
}
