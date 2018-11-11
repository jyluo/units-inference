package units.solvers.backend.gje.encoder;

import backend.gje.GJEFormatTranslator;
import backend.gje.encoder.GJEAbstractConstraintEncoder;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.binary.SubtypeConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import units.representation.TypecheckUnit;
import units.solvers.backend.gje.representation.GJEInferenceUnit;

public class UnitsGJESubtypeConstraintEncoder
        extends GJEAbstractConstraintEncoder<GJEInferenceUnit, TypecheckUnit>
        implements SubtypeConstraintEncoder<String> {

    public UnitsGJESubtypeConstraintEncoder(
            Lattice lattice,
            GJEFormatTranslator<GJEInferenceUnit, TypecheckUnit> gjeFormatTranslator) {
        super(lattice, gjeFormatTranslator);
    }

    protected String encode(Slot subtype, Slot supertype) {
        return null;
        //        return UnitsGJEEncoderUtils.subtype(
        //                subtype.serialize(gjeFormatTranslator),
        //                supertype.serialize(gjeFormatTranslator));
    }

    @Override
    public String encodeVariable_Variable(VariableSlot subtype, VariableSlot supertype) {
        return encode(subtype, supertype);
    }

    @Override
    public String encodeVariable_Constant(VariableSlot subtype, ConstantSlot supertype) {
        return encode(subtype, supertype);
    }

    @Override
    public String encodeConstant_Variable(ConstantSlot subtype, VariableSlot supertype) {
        return encode(subtype, supertype);
    }
}
