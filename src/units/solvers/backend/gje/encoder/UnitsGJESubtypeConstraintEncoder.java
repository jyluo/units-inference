package units.solvers.backend.gje.encoder;

import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.binary.SubtypeConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import units.solvers.backend.gje.UnitsGJEFormatTranslator;
import units.solvers.backend.gje.representation.GJEEquationSet;

public class UnitsGJESubtypeConstraintEncoder extends UnitsGJEAbstractConstraintEncoder
        implements SubtypeConstraintEncoder<GJEEquationSet> {

    public UnitsGJESubtypeConstraintEncoder(
            Lattice lattice, UnitsGJEFormatTranslator formatTranslator) {
        super(lattice, formatTranslator);
    }

    protected GJEEquationSet encode(Slot subtype, Slot supertype) {
        return unitsGJEEncoderUtils.subtype(
                subtype.serialize(formatTranslator), supertype.serialize(formatTranslator));
    }

    @Override
    public GJEEquationSet encodeVariable_Variable(VariableSlot subtype, VariableSlot supertype) {
        return encode(subtype, supertype);
    }

    @Override
    public GJEEquationSet encodeVariable_Constant(VariableSlot subtype, ConstantSlot supertype) {
        return encode(subtype, supertype);
    }

    @Override
    public GJEEquationSet encodeConstant_Variable(ConstantSlot subtype, VariableSlot supertype) {
        return encode(subtype, supertype);
    }
}
