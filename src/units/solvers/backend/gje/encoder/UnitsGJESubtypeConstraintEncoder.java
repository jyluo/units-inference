package units.solvers.backend.gje.encoder;

import backend.gje.GJEFormatTranslator;
import backend.gje.encoder.GJEAbstractConstraintEncoder;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.binary.SubtypeConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import java.util.Map;
import java.util.Set;
import units.representation.TypecheckUnit;
import units.solvers.backend.gje.representation.GJEInferenceUnit;

public class UnitsGJESubtypeConstraintEncoder
        extends GJEAbstractConstraintEncoder<GJEInferenceUnit, TypecheckUnit>
        implements SubtypeConstraintEncoder<Map<String, Set<String>>> {

    public UnitsGJESubtypeConstraintEncoder(
            Lattice lattice,
            GJEFormatTranslator<GJEInferenceUnit, TypecheckUnit> gjeFormatTranslator) {
        super(lattice, gjeFormatTranslator);
    }

    protected Map<String, Set<String>> encode(Slot subtype, Slot supertype) {
        return null;
        //        return UnitsGJEEncoderUtils.subtype(
        //                subtype.serialize(gjeFormatTranslator),
        //                supertype.serialize(gjeFormatTranslator));
    }

    @Override
    public Map<String, Set<String>> encodeVariable_Variable(
            VariableSlot subtype, VariableSlot supertype) {
        return encode(subtype, supertype);
    }

    @Override
    public Map<String, Set<String>> encodeVariable_Constant(
            VariableSlot subtype, ConstantSlot supertype) {
        return encode(subtype, supertype);
    }

    @Override
    public Map<String, Set<String>> encodeConstant_Variable(
            ConstantSlot subtype, VariableSlot supertype) {
        return encode(subtype, supertype);
    }
}
