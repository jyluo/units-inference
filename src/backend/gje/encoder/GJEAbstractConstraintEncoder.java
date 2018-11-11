package backend.gje.encoder;

import backend.gje.GJEFormatTranslator;
import checkers.inference.solver.backend.encoder.AbstractConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;

/** Abstract base class for every Z3Int constraint encoders. */
public class GJEAbstractConstraintEncoder<SlotEncodingT, SlotSolutionT>
        extends AbstractConstraintEncoder<BoolExpr> {

    protected final Context ctx;
    protected final GJEFormatTranslator<SlotEncodingT, SlotSolutionT> gjeFormatTranslator;

    public GJEAbstractConstraintEncoder(
            Lattice lattice,
            Context ctx,
            GJEFormatTranslator<SlotEncodingT, SlotSolutionT> gjeFormatTranslator) {
        // empty value is z3True, contradictory value is z3False
        super(lattice, ctx.mkTrue(), ctx.mkFalse());
        this.ctx = ctx;
        this.gjeFormatTranslator = gjeFormatTranslator;
    }
}
