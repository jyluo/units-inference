package backend.z3smt;

import java.util.HashMap;
import java.util.Map;
import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.AnnotationMirror;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
import checkers.inference.model.ArithmeticVariableSlot;
import checkers.inference.model.CombVariableSlot;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.ExistentialVariableSlot;
import checkers.inference.model.RefinementVariableSlot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.AbstractFormatTranslator;
import checkers.inference.solver.frontend.Lattice;

// <SlotEncodingT, ConstraintEncodingT, SlotSolutionT>
public abstract class Z3SmtFormatTranslator<SlotEncodingT, SlotSolutionT>
        extends AbstractFormatTranslator<SlotEncodingT, BoolExpr, SlotSolutionT> {

    protected Context ctx;

    protected Solver solver;

    protected final Map<Integer, SlotEncodingT> serializedSlots;

    public Z3SmtFormatTranslator(Lattice lattice) {
        super(lattice);
        serializedSlots = new HashMap<>();
    }

    public final void initContext(Context ctx) {
        this.ctx = ctx;
        finishInitializingEncoders();
    }

    public final void initSolver(Solver solver) {
        this.solver = solver;
    }

    /**
     * Add a soft constraint to underlying solver.
     * 
     * @param constraint the soft constraint
     * @param weight the weight of this soft constraint
     * @param group the group of this soft constraint
     */
    protected final void addConstraint(BoolExpr constraint) {
        solver.add(constraint);
    }

    protected abstract SlotEncodingT serializeVarSlot(VariableSlot slot);

    protected abstract SlotEncodingT serializeConstantSlot(ConstantSlot slot);

    @Override
    public SlotEncodingT serialize(VariableSlot slot) {
        return serializeVarSlot(slot);
    }

    @Override
    public SlotEncodingT serialize(ConstantSlot slot) {
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
    public SlotEncodingT serialize(ArithmeticVariableSlot slot) {
        return serializeVarSlot(slot);
    }

    public abstract Map<Integer, AnnotationMirror> decodeSolution(Model model,
            ProcessingEnvironment processingEnv);
}
