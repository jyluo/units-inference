package units.solvers.backend.gje.encoder;

import backend.gje.GJEFormatTranslator;
import backend.gje.encoder.GJEAbstractConstraintEncoder;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.encoder.binary.EqualityConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import java.util.Map;
import java.util.Set;
import units.representation.TypecheckUnit;
import units.solvers.backend.gje.representation.GJEInferenceUnit;

public class UnitsGJEEqualityConstraintEncoder
        extends GJEAbstractConstraintEncoder<GJEInferenceUnit, TypecheckUnit>
        implements EqualityConstraintEncoder<Map<String, Set<String>>> {

    public UnitsGJEEqualityConstraintEncoder(
            Lattice lattice,
            GJEFormatTranslator<GJEInferenceUnit, TypecheckUnit> gjeFormatTranslator) {
        super(lattice, gjeFormatTranslator);
    }

    // 2 Slots are equal if their components are equal
    protected Map<String, Set<String>> encode(Slot fst, Slot snd) {
        return null;
        //        return UnitsGJEEncoderUtils.equality(fst.serialize(gjeFormatTranslator),
        //                snd.serialize(gjeFormatTranslator));
    }

    @Override
    public Map<String, Set<String>> encodeVariable_Variable(VariableSlot fst, VariableSlot snd) {
        return encode(fst, snd);
    }

    @Override
    public Map<String, Set<String>> encodeVariable_Constant(VariableSlot fst, ConstantSlot snd) {
        return encode(fst, snd);
    }

    @Override
    public Map<String, Set<String>> encodeConstant_Variable(ConstantSlot fst, VariableSlot snd) {
        return encode(fst, snd);
    }
}
