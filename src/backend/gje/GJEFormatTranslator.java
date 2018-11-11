package backend.gje;

import checkers.inference.model.CombVariableSlot;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.Constraint;
import checkers.inference.model.ExistentialVariableSlot;
import checkers.inference.model.LubVariableSlot;
import checkers.inference.model.RefinementVariableSlot;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.model.serialization.ToStringSerializer;
import checkers.inference.solver.backend.AbstractFormatTranslator;
import checkers.inference.solver.frontend.Lattice;
import checkers.inference.solver.util.PrintUtils.UniqueSlotCollector;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.AnnotationMirror;
import units.solvers.backend.gje.representation.GJEEquationSet;

// AbstractFormatTranslator<SlotEncodingT, ConstraintEncodingT, SlotSolutionT>
public abstract class GJEFormatTranslator<SlotEncodingT, SlotSolutionT>
        extends AbstractFormatTranslator<SlotEncodingT, GJEEquationSet, SlotSolutionT> {

    /** Cache of all serialized slots, keyed on slot ID. */
    protected final Map<Integer, SlotEncodingT> serializedSlots = new HashMap<>();

    // maps serialized slot ID to the slot objects
    protected final Map<Integer, Slot> slotGJEtoCFIMap = new HashMap<>();
    protected final Map<Slot, Integer> slotCFItoGJEMap = new HashMap<>();

    public GJEFormatTranslator(Lattice lattice) {
        super(lattice);
        finishInitializingEncoders();
    }

    protected int assignGJEVarIDs(Collection<Constraint> constraints) {
        int gjeID = 0;

        final ToStringSerializer toStringSerializer = new ToStringSerializer(false);

        System.out.println("== Slot serialization map ==");
        // get a set of unique slots used in the constraints
        UniqueSlotCollector slotsCollector = new UniqueSlotCollector();
        for (Constraint constraint : constraints) {
            constraint.serialize(slotsCollector);
        }

        for (VariableSlot slot : slotsCollector.getSlots()) {
            slotGJEtoCFIMap.put(gjeID, slot);
            slotCFItoGJEMap.put(slot, gjeID);
            System.out.println("ID: " + gjeID + " --> slot " + slot.serialize(toStringSerializer));
            gjeID++;
        }

        return gjeID;
    }

    protected abstract SlotEncodingT serializeVarSlot(VariableSlot slot);

    protected abstract SlotEncodingT serializeConstantSlot(ConstantSlot slot);

    @Override
    public SlotEncodingT serialize(VariableSlot slot) {
        // System.out.println("Serializing vs " + slot);
        return serializeVarSlot(slot);
    }

    @Override
    public SlotEncodingT serialize(ConstantSlot slot) {
        // System.out.println("Serializing cs " + slot);
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
