package units.solvers.backend.gje.encoder;

import backend.gje.GJEFormatTranslator;
import backend.gje.encoder.GJEAbstractConstraintEncoder;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.binary.SubtypeConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import units.representation.InferenceUnit;
import units.representation.TypecheckUnit;
import units.util.UnitsGJEEncoderUtils;

public class UnitsGJESubtypeConstraintEncoder
        extends GJEAbstractConstraintEncoder<InferenceUnit, TypecheckUnit>
        implements SubtypeConstraintEncoder<BoolExpr> {

    public UnitsGJESubtypeConstraintEncoder(
            Lattice lattice,
            Context ctx,
            GJEFormatTranslator<InferenceUnit, TypecheckUnit> z3SmtFormatTranslator) {
        super(lattice, ctx, z3SmtFormatTranslator);
    }

    protected BoolExpr encode(Slot subtype, Slot supertype) {
        return UnitsGJEEncoderUtils.subtype(
                ctx,
                subtype.serialize(gjeFormatTranslator),
                supertype.serialize(gjeFormatTranslator));
    }

    @Override
    public BoolExpr encodeVariable_Variable(VariableSlot subtype, VariableSlot supertype) {
        return encode(subtype, supertype);
    }

    @Override
    public BoolExpr encodeVariable_Constant(VariableSlot subtype, ConstantSlot supertype) {
        return encode(subtype, supertype);
    }

    @Override
    public BoolExpr encodeConstant_Variable(ConstantSlot subtype, VariableSlot supertype) {
        return encode(subtype, supertype);
    }
}
