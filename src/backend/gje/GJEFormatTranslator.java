package backend.gje;

import checkers.inference.model.CombVariableSlot;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.ExistentialVariableSlot;
import checkers.inference.model.LubVariableSlot;
import checkers.inference.model.RefinementVariableSlot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.AbstractFormatTranslator;
import checkers.inference.solver.frontend.Lattice;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.AnnotationMirror;

// AbstractFormatTranslator<SlotEncodingT, ConstraintEncodingT, SlotSolutionT>
public abstract class GJEFormatTranslator<SlotEncodingT, SlotSolutionT>
        extends AbstractFormatTranslator<SlotEncodingT, String, SlotSolutionT> {

    /** Cache of all serialized slots, keyed on slot ID. */
    protected final Map<Integer, SlotEncodingT> serializedSlots = new HashMap<>();

    public GJEFormatTranslator(Lattice lattice) {
        super(lattice);
        finishInitializingEncoders();
    }

    // public final void init(Context ctx) {
    // finishInitializingEncoders();
    // }

    protected abstract SlotEncodingT serializeVarSlot(VariableSlot slot);

    protected abstract SlotEncodingT serializeConstantSlot(ConstantSlot slot);

    @Override
    public SlotEncodingT serialize(VariableSlot slot) {
        System.out.println("Serializing vs " + slot);
        return serializeVarSlot(slot);
    }

    @Override
    public SlotEncodingT serialize(ConstantSlot slot) {
        System.out.println("Serializing cs " + slot);
        return serializeConstantSlot(slot);
    }

    @Override
    public SlotEncodingT serialize(ExistentialVariableSlot slot) {
        return serializeVarSlot(slot);
    }

    @Override
    public SlotEncodingT serialize(RefinementVariableSlot slot) {
        return serializeVarSlot(slot);
    }

    @Override
    public SlotEncodingT serialize(CombVariableSlot slot) {
        return serializeVarSlot(slot);
    }

    @Override
    public SlotEncodingT serialize(LubVariableSlot slot) {
        return serializeVarSlot(slot);
    }

    public abstract Map<Integer, AnnotationMirror> decodeSolution(
            List<String> model, ProcessingEnvironment processingEnv);
}
