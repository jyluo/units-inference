package backend.z3smt.encoder;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import backend.z3smt.Z3SmtFormatTranslator;
import checkers.inference.solver.backend.encoder.AbstractConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;

/**
 * Abstract base class for every Z3Int constraint encoders.
 */
public class Z3SmtAbstractConstraintEncoder<SlotEncodingT, SlotSolutionT>
        extends AbstractConstraintEncoder<BoolExpr> {

    protected final Context ctx;
    protected final Z3SmtFormatTranslator<SlotEncodingT, SlotSolutionT> z3IntFormatTranslator;

    public Z3SmtAbstractConstraintEncoder(Lattice lattice, Context ctx,
            Z3SmtFormatTranslator<SlotEncodingT, SlotSolutionT> z3IntFormatTranslator) {
        // empty value is z3True, contradictory value is z3False
        super(lattice, ctx.mkTrue(), ctx.mkFalse());
        this.ctx = ctx;
        this.z3IntFormatTranslator = z3IntFormatTranslator;
    }
}
