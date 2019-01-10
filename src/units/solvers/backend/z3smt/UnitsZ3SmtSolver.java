package units.solvers.backend.z3smt;

import backend.z3smt.Z3SmtFormatTranslator;
import backend.z3smt.Z3SmtSolver;
import checkers.inference.InferenceMain;
import checkers.inference.model.ComparableConstraint;
import checkers.inference.model.Constraint;
import checkers.inference.model.Slot;
import checkers.inference.model.SubtypeConstraint;
import checkers.inference.model.VariableSlot;
import checkers.inference.model.serialization.ToStringSerializer;
import checkers.inference.solver.frontend.Lattice;
import checkers.inference.solver.util.ExternalSolverUtils;
import checkers.inference.solver.util.FileUtils;
import checkers.inference.solver.util.SolverEnvironment;
import com.microsoft.z3.Expr;
import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import org.checkerframework.javacutil.BugInCF;
import units.representation.TypecheckUnit;
import units.representation.UnitsRepresentationUtils;
import units.solvers.backend.z3smt.representation.Z3EquationSet;
import units.solvers.backend.z3smt.representation.Z3InferenceUnit;

public class UnitsZ3SmtSolver extends Z3SmtSolver<Z3InferenceUnit, Z3EquationSet, TypecheckUnit> {

    final UnitsRepresentationUtils unitsRep;

    final Map<String, StringBuffer> fileContents = new HashMap<>();

    public UnitsZ3SmtSolver(
            SolverEnvironment solverEnvironment,
            Collection<Slot> slots,
            Collection<Constraint> constraints,
            Z3SmtFormatTranslator<Z3InferenceUnit, Z3EquationSet, TypecheckUnit>
                    z3SmtFormatTranslator,
            Lattice lattice) {
        super(solverEnvironment, slots, constraints, z3SmtFormatTranslator, lattice);
        unitsRep = UnitsRepresentationUtils.getInstance();
    }

    @Override
    protected void serializeSMTFileContents() {
        serializationStart = System.currentTimeMillis();
        encodeAllSlots();
        encodeAllConstraints();
        serializationEnd = System.currentTimeMillis();

        System.err.println("Encoding constraints done!");

        for (Entry<String, StringBuffer> entry : fileContents.entrySet()) {
            StringBuffer buffer = entry.getValue();

            buffer.append("(check-sat)" + System.lineSeparator());
            if (mode == Mode.GetUnsatCore) {
                buffer.append("(get-unsat-core)" + System.lineSeparator());
            } else {
                buffer.append("(get-model)" + System.lineSeparator());
            }
        }

        writeConstraintsToSMTFile();
    }

    @Override
    protected void writeConstraintsToSMTFile() {

        System.err.println("Writing constraints to files: ");

        if (!(mode == Mode.GetUnsatCore)) {
            // write the constraints to the files for external solver use
            for (Entry<String, StringBuffer> entry : fileContents.entrySet()) {
                File dest = new File(getConstraintFileName(entry.getKey()));
                System.err.println("  " + dest.toString());
                FileUtils.writeFile(dest, entry.getValue().toString());
            }
        } else {
            // write the constraints to the files for external solver use
            for (Entry<String, StringBuffer> entry : fileContents.entrySet()) {
                File dest = new File(getUnsatCoreConstraintFileName(entry.getKey()));
                System.err.println("  " + dest.toString());
                FileUtils.writeFile(dest, entry.getValue().toString());
            }
        }

        // write a copy in append mode to stats files for later bulk analysis
        for (Entry<String, StringBuffer> entry : fileContents.entrySet()) {
            File dest =
                    new File(
                            pathToProject
                                    + constraintsStatsFilePrefix
                                    + entry.getKey()
                                    + smtExtension);
            System.err.println("  " + dest.toString());
            FileUtils.appendFile(dest, entry.getValue().toString());
        }
    }

    @Override
    protected void encodeAllSlots() {
        // preprocess slots
        formatTranslator.preAnalyzeSlots(slots);

        // create string buffers for the file contents
        if (unitsRep.serializeOnlyTopAndBot()) {
            createBufferAndPutSmtFileHeader(Z3EquationSet.topAndBottomKey);
        }

        if (unitsRep.serializePrefix()) {
            createBufferAndPutSmtFileHeader(Z3EquationSet.prefixExponentKey);
        }

        for (String baseUnit : unitsRep.serializableBaseUnits()) {
            createBufferAndPutSmtFileHeader(baseUnit);
        }

        // build definitions for slots
        for (Slot slot : slots) {
            if (slot.isVariable()) {

                Map<String, String> slotDeclarations =
                        formatTranslator.generateZ3SlotDeclaration((VariableSlot) slot);

                System.err.println(slotDeclarations);

                if (unitsRep.serializeOnlyTopAndBot()) {
                    appendSlotDeclaration(slotDeclarations, Z3EquationSet.topAndBottomKey);
                }

                if (unitsRep.serializePrefix()) {
                    appendSlotDeclaration(slotDeclarations, Z3EquationSet.prefixExponentKey);
                }

                for (String baseUnit : unitsRep.serializableBaseUnits()) {
                    appendSlotDeclaration(slotDeclarations, baseUnit);
                }
            }
        }

        // generate slot constraints
        for (Slot slot : slots) {
            if (slot.isVariable()) {
                VariableSlot varSlot = (VariableSlot) slot;

                final Z3EquationSet wfConstraints =
                        formatTranslator.encodeSlotWellformnessConstraint(varSlot);

                if (unitsRep.serializeOnlyTopAndBot()) {
                    appendConstraintToFile(wfConstraints, Z3EquationSet.topAndBottomKey);
                }

                if (unitsRep.serializePrefix()) {
                    appendConstraintToFile(wfConstraints, Z3EquationSet.prefixExponentKey);
                }

                for (String baseUnit : unitsRep.serializableBaseUnits()) {
                    appendConstraintToFile(wfConstraints, baseUnit);
                }

                if (mode == Mode.OptimizingMode) {
                    final Z3EquationSet prefConstraints =
                            formatTranslator.encodeSlotPreferenceConstraint(varSlot);

                    if (unitsRep.serializeOnlyTopAndBot()) {
                        appendSoftConstraintToFile(prefConstraints, Z3EquationSet.topAndBottomKey);
                    }

                    if (unitsRep.serializePrefix()) {
                        appendSoftConstraintToFile(
                                prefConstraints, Z3EquationSet.prefixExponentKey);
                    }

                    for (String baseUnit : unitsRep.serializableBaseUnits()) {
                        appendSoftConstraintToFile(prefConstraints, baseUnit);
                    }
                }
            }
        }

        // debug dump of just slot definitions
        for (Entry<String, StringBuffer> entry : fileContents.entrySet()) {
            FileUtils.appendFile(
                    new File(pathToProject + "/slots" + entry.getKey() + smtExtension),
                    entry.getValue().toString());
        }
    }

    void createBufferAndPutSmtFileHeader(String key) {
        StringBuffer buffer = new StringBuffer();
        // only enable in unsat core mode
        if (mode == Mode.GetUnsatCore) {
            buffer.append("(set-option :produce-unsat-cores true)\n");
        }
        fileContents.put(key, buffer);
    }

    void appendSlotDeclaration(Map<String, String> slotDeclarations, String key) {
        fileContents.get(key).append(slotDeclarations.get(key));
    }

    void appendConstraintToFile(Z3EquationSet constraints, String key) {
        Expr constraint = constraints.getEquation(key).simplify();
        if (!constraint.isTrue()) {
            fileContents.get(key).append(z3Assert(constraint));
        }
    }

    void appendSoftConstraintToFile(Z3EquationSet constraints, String key) {
        Expr constraint = constraints.getEquation(key).simplify();
        if (!constraint.isTrue()) {
            fileContents.get(key).append(z3SoftAssert(constraint));
        }
    }

    // =======================================================================================

    @Override
    protected void encodeAllConstraints() {
        int current = 1;

        for (Constraint constraint : constraints) {
            // System.err.println("Getting next item.");

            // System.err.println(
            // " Serializing Constraint " + current + " / " + total + " : " +
            // constraint);

            // if (current % 100 == 0) {
            // System.err.println("=== Running GC ===");
            // Runtime.getRuntime().gc(); // trigger garbage collector
            // }

            Z3EquationSet serializedConstraintSet = constraint.serialize(formatTranslator);

            // System.err.println(" Constraint serialized. ");

            if (serializedConstraintSet == null) {
                // TODO: Should error abort if unsupported constraint detected.
                // Currently warning is a workaround for making ontology
                // working, as in some cases existential constraints generated.
                // Should investigate on this, and change this to ErrorAbort
                // when eliminated unsupported constraints.
                System.err.println(
                        "Unsupported constraint detected! Constraint type: "
                                + constraint.getClass().getSimpleName());
                // current++;
                continue;
            }

            // System.err.println(" Constraint \n" + serializedConstraint
            // + "\n simplified :\n " + serializedConstraint.simplify());

            // store simplified constraints for serialization
            Expr simplifiedConstraintForTopAndBottom = null;
            Expr simplifiedConstraintForPrefix = null;
            Map<String, Expr> simplifiedConstraintsForAllBaseUnits = new HashMap<>();

            // skip if all subconstraints are serialized to true
            if (unitsRep.serializeOnlyTopAndBot()) {
                simplifiedConstraintForTopAndBottom =
                        serializedConstraintSet
                                .getEquation(Z3EquationSet.topAndBottomKey)
                                .simplify();
                // only 1 constraint equation to check
                if (simplifiedConstraintForTopAndBottom.isTrue()) {
                    continue;
                }
            }

            int numOfTrue = 0;
            int numOfFalse = 0;

            if (unitsRep.serializePrefix()) {
                simplifiedConstraintForPrefix =
                        serializedConstraintSet
                                .getEquation(Z3EquationSet.prefixExponentKey)
                                .simplify();

                if (simplifiedConstraintForPrefix.isTrue()) {
                    numOfTrue++;
                }

                if (simplifiedConstraintForPrefix.isFalse()) {
                    numOfFalse++;
                }
            }

            for (String baseUnit : unitsRep.serializableBaseUnits()) {

                Expr simplifiedConstraintForBaseUnit =
                        serializedConstraintSet.getEquation(baseUnit).simplify();

                if (simplifiedConstraintForBaseUnit.isTrue()) {
                    numOfTrue++;
                }

                if (simplifiedConstraintForBaseUnit.isFalse()) {
                    numOfFalse++;
                }

                simplifiedConstraintsForAllBaseUnits.put(baseUnit, simplifiedConstraintForBaseUnit);
            }

            int requiredCount = unitsRep.serializePrefix() ? 1 : 0;
            requiredCount += unitsRep.serializableBaseUnits().size();

            // if all are true, skip tautology
            if (numOfTrue == requiredCount) {
                continue;
            }

            // if any sub-constraint is false, create error
            if (numOfFalse > 0) {
                final ToStringSerializer toStringSerializer = new ToStringSerializer(false);
                throw new BugInCF(
                        "impossible constraint: "
                                + constraint.serialize(toStringSerializer)
                                + "\nSerialized:\n"
                                + serializedConstraintSet);
            }

            // serialize required constraints
            if (mode == Mode.SatMode || mode == Mode.OptimizingMode) {
                if (unitsRep.serializeOnlyTopAndBot()) {
                    fileContents
                            .get(Z3EquationSet.topAndBottomKey)
                            .append(z3Assert(simplifiedConstraintForTopAndBottom));
                }

                if (unitsRep.serializePrefix()) {
                    fileContents
                            .get(Z3EquationSet.prefixExponentKey)
                            .append(z3Assert(simplifiedConstraintForPrefix));
                }

                for (String baseUnit : unitsRep.serializableBaseUnits()) {
                    fileContents
                            .get(baseUnit)
                            .append(z3Assert(simplifiedConstraintsForAllBaseUnits.get(baseUnit)));
                }
            }

            // serialize preference constraints
            if (mode == Mode.OptimizingMode) {

                if (constraint instanceof SubtypeConstraint) {
                    // generate a soft constraint that we prefer equality for subtype
                    // TODO: perhaps prefer not bottom and prefer not top will suffice?
                    SubtypeConstraint stConstraint = (SubtypeConstraint) constraint;

                    Constraint eqConstraint =
                            InferenceMain.getInstance()
                                    .getConstraintManager()
                                    .createEqualityConstraint(
                                            stConstraint.getSubtype(), stConstraint.getSupertype());

                    Z3EquationSet eqConstraints = eqConstraint.serialize(formatTranslator);

                    if (unitsRep.serializeOnlyTopAndBot()) {
                        appendSoftConstraintToFile(eqConstraints, Z3EquationSet.topAndBottomKey);
                    }

                    if (unitsRep.serializePrefix()) {
                        appendSoftConstraintToFile(eqConstraints, Z3EquationSet.prefixExponentKey);
                    }

                    for (String baseUnit : unitsRep.serializableBaseUnits()) {
                        appendSoftConstraintToFile(eqConstraints, baseUnit);
                    }

                } else if (constraint instanceof ComparableConstraint) {
                    // generate soft constraint for comparisons that their args are equal
                    ComparableConstraint compConstraint = (ComparableConstraint) constraint;

                    Constraint eqConstraint =
                            InferenceMain.getInstance()
                                    .getConstraintManager()
                                    .createEqualityConstraint(
                                            compConstraint.getFirst(), compConstraint.getSecond());

                    Z3EquationSet eqConstraints = eqConstraint.serialize(formatTranslator);

                    if (unitsRep.serializeOnlyTopAndBot()) {
                        appendSoftConstraintToFile(eqConstraints, Z3EquationSet.topAndBottomKey);
                    }

                    if (unitsRep.serializePrefix()) {
                        appendSoftConstraintToFile(eqConstraints, Z3EquationSet.prefixExponentKey);
                    }

                    for (String baseUnit : unitsRep.serializableBaseUnits()) {
                        appendSoftConstraintToFile(eqConstraints, baseUnit);
                    }
                }
            }

            // serialize unsat core constraints
            if (mode == Mode.GetUnsatCore) {
                // add assertions with names, for unsat core dump
                String constraintName = constraint.getClass().getSimpleName() + current;

                if (unitsRep.serializeOnlyTopAndBot()) {
                    fileContents
                            .get(Z3EquationSet.topAndBottomKey)
                            .append(
                                    z3UnsatCoreAssert(
                                            simplifiedConstraintForTopAndBottom, constraintName));
                }

                if (unitsRep.serializePrefix()) {
                    fileContents
                            .get(Z3EquationSet.prefixExponentKey)
                            .append(
                                    z3UnsatCoreAssert(
                                            simplifiedConstraintForPrefix, constraintName));
                }

                for (String baseUnit : unitsRep.serializableBaseUnits()) {
                    fileContents
                            .get(baseUnit)
                            .append(
                                    z3UnsatCoreAssert(
                                            simplifiedConstraintsForAllBaseUnits.get(baseUnit),
                                            constraintName));
                }

                // add constraint to serialized constraints map, so that we can
                // retrieve later using the constraint name when outputting the unsat core
                serializedConstraints.put(constraintName, constraint);
            }

            current++;
            // System.err.println(" Added constraint. HasNext? " + iter.hasNext());
        }

        // debug dump of slot and constraint definitions
        for (Entry<String, StringBuffer> entry : fileContents.entrySet()) {
            FileUtils.appendFile(
                    new File(pathToProject + "/constraints" + entry.getKey() + smtExtension),
                    entry.getValue().toString());
        }
    }

    private String getConstraintFileName(String key) {
        return pathToProject + constraintsFilePrefix + key + smtExtension;
    }

    private String getUnsatCoreConstraintFileName(String key) {
        return pathToProject + constraintsUnsatCoreFilePrefix + key + smtExtension;
    }

    @Override
    protected List<String> runZ3Solver() {
        List<String[]> commands = new ArrayList<>();

        if (!(mode == Mode.GetUnsatCore)) {
            for (Entry<String, StringBuffer> entry : fileContents.entrySet()) {
                commands.add(new String[] {z3Program, getConstraintFileName(entry.getKey())});
            }
        } else {
            for (Entry<String, StringBuffer> entry : fileContents.entrySet()) {
                commands.add(
                        new String[] {z3Program, getUnsatCoreConstraintFileName(entry.getKey())});
            }
        }

        String[] command;

        return null;
    }

    // run a single z3 instance
    private List<String> runZ3Solver(String[] command) {
        // stores results from z3 program output
        final List<String> results = new ArrayList<>();

        // Run command
        // TODO: check that stdErr has no errors
        int exitStatus =
                ExternalSolverUtils.runExternalSolver(
                        command,
                        stdOut -> parseStdOut(stdOut, results),
                        stdErr -> ExternalSolverUtils.printStdStream(System.err, stdErr));
        // if exit status from z3 is not 0, then it is unsat
        return exitStatus == 0 ? results : null;
    }
}
