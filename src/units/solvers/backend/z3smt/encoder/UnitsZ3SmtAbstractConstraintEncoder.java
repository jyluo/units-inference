package units.solvers.backend.z3smt.encoder;

import backend.z3smt.encoder.Z3SmtAbstractConstraintEncoder;
import checkers.inference.solver.frontend.Lattice;
import com.microsoft.z3.Context;
import units.solvers.backend.z3smt.UnitsZ3SmtFormatTranslator;
import units.solvers.backend.z3smt.representation.Z3InferenceUnit;
import units.utils.TypecheckUnit;
import units.utils.UnitsRepresentationUtils;
import units.utils.UnitsTypecheckUtils;

/** Abstract base class for every Z3Int constraint encoders. */
public class UnitsZ3SmtAbstractConstraintEncoder
        extends Z3SmtAbstractConstraintEncoder<Z3InferenceUnit, TypecheckUnit> {

    protected final UnitsRepresentationUtils unitsRepUtils;

    protected final UnitsZ3SmtEncoderUtils unitsZ3SmtEncoderUtils;

    protected final UnitsTypecheckUtils unitsTypecheckUtils;

    public UnitsZ3SmtAbstractConstraintEncoder(
            Lattice lattice, Context ctx, UnitsZ3SmtFormatTranslator unitsZ3SmtFormatTranslator) {
        super(lattice, ctx, unitsZ3SmtFormatTranslator);
        this.unitsRepUtils = unitsZ3SmtFormatTranslator.getUnitsRepresentationUtils();
        this.unitsZ3SmtEncoderUtils = unitsZ3SmtFormatTranslator.getUnitsZ3SmtEncoderUtils();
        this.unitsTypecheckUtils = unitsZ3SmtFormatTranslator.getUnitsTypecheckUtils();
    }
}
