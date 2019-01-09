package backend.z3smt;

import checkers.inference.model.ArithmeticConstraint;
import checkers.inference.model.ArithmeticConstraint.ArithmeticOperationKind;
import checkers.inference.model.Constraint;
import checkers.inference.model.Slot;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.Solver;
import checkers.inference.solver.frontend.Lattice;
import checkers.inference.solver.util.ExternalSolverUtils;
import checkers.inference.solver.util.FileUtils;
import checkers.inference.solver.util.SolverArg;
import checkers.inference.solver.util.SolverEnvironment;
import checkers.inference.solver.util.Statistics;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import javax.lang.model.element.AnnotationMirror;

// TODO: make this an abstract class with common features
public abstract class Z3SmtSolver<SlotEncodingT, ConstraintEncodingT, SlotSolutionT>
        extends Solver<Z3SmtFormatTranslator<SlotEncodingT, ConstraintEncodingT, SlotSolutionT>> {

    public enum Z3SolverEngineArg implements SolverArg {
        /** option to use optimizing mode or not */
        optimizingMode
    }

    protected final Context ctx;
    protected com.microsoft.z3.Optimize solver;
    protected StringBuffer smtFileContents;

    protected static final String z3Program = "z3";
    protected boolean optimizingMode;
    protected boolean getUnsatCore;

    // used in non-optimizing mode to find unsat constraints
    protected final Map<String, Constraint> serializedConstraints = new HashMap<>();
    protected final List<String> unsatConstraintIDs = new ArrayList<>();

    // file is written at projectRootFolder/constraints.smt
    protected static final String pathToProject =
            new File(new File("").getAbsolutePath()).toString();
    protected static final String constraintsFile = pathToProject + "/z3Constraints.smt";
    protected static final String constraintsUnsatCoreFile =
            pathToProject + "/z3ConstraintsUnsatCore.smt";
    protected static final String constraintsStatsFile = pathToProject + "/z3ConstraintsGlob.smt";

    // timing statistics variables
    protected long serializationStart;
    protected long serializationEnd;
    protected long solvingStart;
    protected long solvingEnd;

    public Z3SmtSolver(
            SolverEnvironment solverEnvironment,
            Collection<Slot> slots,
            Collection<Constraint> constraints,
            Z3SmtFormatTranslator<SlotEncodingT, ConstraintEncodingT, SlotSolutionT>
                    z3SmtFormatTranslator,
            Lattice lattice) {
        super(solverEnvironment, slots, constraints, z3SmtFormatTranslator, lattice);

        // creating solver with timeout
        // Map<String, String> z3Args = new HashMap<>();
        // int timeout = 2 * 60 * 1000; // timeout of 2 mins
        // z3Args.put("timeout", Integer.toString(timeout));
        // ctx = new Context(z3Args);

        // creating solver without timeout
        ctx = new Context();

        z3SmtFormatTranslator.init(ctx);
    }

    // Main entry point
    @Override
    public Map<Integer, AnnotationMirror> solve() {
        Map<Integer, AnnotationMirror> result;

        // serialize based on user choice of running in optimizing or non-optimizing mode
        optimizingMode = solverEnvironment.getBoolArg(Z3SolverEngineArg.optimizingMode);
        getUnsatCore = false;

        if (optimizingMode) {
            System.err.println("Encoding for optimizing mode");
        } else {
            System.err.println("Encoding for non-optimizing mode");
        }

        serializeSMTFileContents();

        solvingStart = System.currentTimeMillis();
        // in Units, if the status is SAT then there must be output in the model
        List<String> results = runZ3Solver();
        solvingEnd = System.currentTimeMillis();

        Statistics.addOrIncrementEntry(
                "smt_serialization_time(millisec)", serializationEnd - serializationStart);
        Statistics.addOrIncrementEntry("smt_solving_time(millisec)", solvingEnd - solvingStart);

        // Debug use, finds out number of calls to each instrumented method
        // TODO: use updated stats package to print out the counters
        System.err.println("=== Arithmetic Constraints Printout ===");
        Map<ArithmeticOperationKind, Integer> arithmeticConstraintCounters = new HashMap<>();
        for (ArithmeticOperationKind kind : ArithmeticOperationKind.values()) {
            arithmeticConstraintCounters.put(kind, 0);
        }
        for (Constraint constraint : constraints) {
            if (constraint instanceof ArithmeticConstraint) {
                ArithmeticConstraint arithmeticConstraint = (ArithmeticConstraint) constraint;
                ArithmeticOperationKind kind = arithmeticConstraint.getOperation();
                arithmeticConstraintCounters.put(kind, arithmeticConstraintCounters.get(kind) + 1);
            }
        }
        for (ArithmeticOperationKind kind : ArithmeticOperationKind.values()) {
            System.err.println(
                    " Made arithmetic "
                            + kind.getSymbol()
                            + " constraint: "
                            + arithmeticConstraintCounters.get(kind));
        }

        // TODO: update parse scripts to interpret output of
        // "comparableconstraint"
        // System.err.println("=== Comparison Constraints Printout ===");
        // int comparableConstraints = 0;
        // for (Constraint constraint : constraints) {
        // if (constraint instanceof ComparableConstraint) {
        // comparableConstraints++;
        // }
        // }
        // System.err.println(" Made comparison constraint: " +
        // comparableConstraints);

        if (results != null) {
            result =
                    formatTranslator.decodeSolution(
                            results, solverEnvironment.processingEnvironment);
        } else {
            System.err.println("\n\n!!! The set of constraints is unsatisfiable! !!!");
            result = null;
        }

        return result;
    }

    @Override
    public Collection<Constraint> explainUnsatisfiable() {
        optimizingMode = false;
        getUnsatCore = true;

        System.err.println("Now encoding for unsat core dump.");
        serializeSMTFileContents();

        solvingStart = System.currentTimeMillis();
        runZ3Solver();
        solvingEnd = System.currentTimeMillis();

        Statistics.addOrIncrementEntry(
                "smt_unsat_serialization_time(millisec)", serializationEnd - serializationStart);
        Statistics.addOrIncrementEntry(
                "smt_unsat_solving_time(millisec)", solvingEnd - solvingStart);

        // System.err.println();
        // System.err.println("Unsatisfiable constraints: " + String.join(" ",
        // unsatConstraintIDs));
        // System.err.println();

        List<Constraint> unsatConstraints = new ArrayList<>();

        for (String constraintID : unsatConstraintIDs) {
            Constraint c = serializedConstraints.get(constraintID);
            // System.err.println(constraintID + " :");
            // System.err.println(c);
            // System.err.println(c.getLocation());
            // System.err.println();
            unsatConstraints.add(c);
        }

        return unsatConstraints;
    }

    private void serializeSMTFileContents() {
        // make a fresh solver to contain encodings of the slots
        solver = ctx.mkOptimize();
        // make a new buffer to store the serialized smt file contents
        smtFileContents = new StringBuffer();

        // only enable in non-optimizing mode
        if (!optimizingMode && getUnsatCore) {
            smtFileContents.append("(set-option :produce-unsat-cores true)\n");
        }

        serializationStart = System.currentTimeMillis();
        encodeAllSlots();
        encodeAllConstraints();
        serializationEnd = System.currentTimeMillis();

        System.err.println("Encoding constraints done!");

        smtFileContents.append("(check-sat)\n");
        if (!optimizingMode && getUnsatCore) {
            smtFileContents.append("(get-unsat-core)\n");
        } else {
            smtFileContents.append("(get-model)\n");
        }

        System.err.println("Writing constraints to file: " + constraintsFile);

        writeConstraintsToSMTFile();
    }

    private void writeConstraintsToSMTFile() {
        String fileContents = smtFileContents.toString();

        if (!getUnsatCore) {
            // write the constraints to the file for external solver use
            FileUtils.writeFile(new File(constraintsFile), fileContents);
        } else {
            // write the constraints to the file for external solver use
            FileUtils.writeFile(new File(constraintsUnsatCoreFile), fileContents);
        }
        // write a copy in append mode to stats file for later bulk analysis
        FileUtils.appendFile(new File(constraintsStatsFile), fileContents);
    }
    //
    //    private String generateZ3Constraint(BoolExpr serializedConstraint, String constraintSource) {
    //        Expr simplifiedConstraint = serializedConstraint.simplify();
    //
    //        if (simplifiedConstraint.isTrue()) {
    //            // This only works if the BoolExpr is directly the value Z3True.
    //            // Still a good
    //            // filter, but doesn't filter enough.
    //            // EG: (and (= false false) (= false false) (= 0 0) (= 0 0) (= 0
    //            // 0))
    //            // Skip tautology.
    //            // System.err.println(" simplified to tautology.");
    //            return "";
    //        }
    //
    //        if (simplifiedConstraint.isFalse()) {
    //            throw new BugInCF("impossible constraint: " + constraintSource);
    //        }
    //
    //        // TODO: properly support adding wellformedness constraint as a debug output option for unsat dump
    //
    //        return generateZ3Constraint(simplifiedConstraint.toString());
    //    }
    //
    //    private String generateZ3Constraint(String clause) {
    //        return "(assert " + clause + ")" + System.lineSeparator();
    //    }
    //
    //    private String generateZ3UnsatCoreConstraint(String clause, String constraintName) {
    //        return "(assert (! " + clause + " :named " + constraintName + "))" + System.lineSeparator();
    //    }
    //
    //    private void addConstraint(BoolExpr serializedConstraint, Constraint constraint) {
    //        Expr simplifiedConstraint = serializedConstraint.simplify();
    //
    //        if (simplifiedConstraint.isTrue()) {
    //            // This only works if the BoolExpr is directly the value Z3True.
    //            // Still a good
    //            // filter, but doesn't filter enough.
    //            // EG: (and (= false false) (= false false) (= 0 0) (= 0 0) (= 0
    //            // 0))
    //            // Skip tautology.
    //            // System.err.println(" simplified to tautology.");
    //            return;
    //        }
    //
    //        if (simplifiedConstraint.isFalse()) {
    //            final ToStringSerializer toStringSerializer = new ToStringSerializer(false);
    //            throw new BugInCF(
    //                    "impossible constraint: "
    //                            + constraint.serialize(toStringSerializer)
    //                            + "\nSerialized:\n"
    //                            + serializedConstraint);
    //        }
    //
    //        solver.Assert(serializedConstraint);
    //    }
    //
    //    private void addSoftConstraint(Constraint constraint, BoolExpr serializedConstraint) {
    //        Expr simplifiedConstraint = serializedConstraint.simplify();
    //
    //        if (simplifiedConstraint.isTrue()) {
    //            // This only works if the BoolExpr is directly the value Z3True.
    //            // Still a good
    //            // filter, but doesn't filter enough.
    //            // EG: (and (= false false) (= false false) (= 0 0) (= 0 0) (= 0
    //            // 0))
    //            // Skip tautology.
    //            // System.err.println(" simplified to tautology.");
    //            return;
    //        }
    //
    //        if (simplifiedConstraint.isFalse()) {
    //            final ToStringSerializer toStringSerializer = new ToStringSerializer(false);
    //            throw new BugInCF(
    //                    "impossible constraint: "
    //                            + constraint.serialize(toStringSerializer)
    //                            + "\nSerialized:\n"
    //                            + serializedConstraint);
    //        }
    //
    //        solver.AssertSoft(serializedConstraint);
    //    }

    protected void encodeAllSlots() {
        // preprocess slots
        formatTranslator.preAnalyzeSlots(slots);

        //        StringBuilder z3SlotDefinitions = new StringBuilder();
        //
        //        // generate slot definitions
        //        for (Slot slot : slots) {
        //            if (slot.isVariable()) {
        //                String slotDefinition =
        //                        formatTranslator.generateZ3SlotDeclaration((VariableSlot) slot);
        //                System.err.println(slotDefinition);
        //                z3SlotDefinitions.append(slotDefinition);
        //            }
        //        }

        // generate slot constraints
        for (Slot slot : slots) {
            if (slot.isVariable()) {
                VariableSlot varSlot = (VariableSlot) slot;

                BoolExpr wfConstraint = formatTranslator.encodeSlotWellformnessConstraint(varSlot);

                if (!wfConstraint.simplify().isTrue()) {
                    solver.Assert(wfConstraint);
                }
                if (optimizingMode) {
                    // empty string means no optimization group
                    solver.AssertSoft(
                            formatTranslator.encodeSlotPreferenceConstraint(varSlot), 1, "");
                }
            }
        }

        // solver.toString() also includes "(check-sat)" as the last line,
        // remove it
        String slotDefinitionsAndConstraints = solver.toString();
        int truncateIndex = slotDefinitionsAndConstraints.lastIndexOf("(check-sat)");
        assert truncateIndex != -1;

        // append slot definitions to overall smt file
        smtFileContents.append(slotDefinitionsAndConstraints.substring(0, truncateIndex));

        // debug use:
        // Write Slots to file
        FileUtils.appendFile(new File(pathToProject + "/slots.smt"), solver.toString());
    }

    private List<String> runZ3Solver() {
        // TODO: add z3 stats?
        String[] command;
        if (!getUnsatCore) {
            command = new String[] {z3Program, constraintsFile};
        } else {
            command = new String[] {z3Program, constraintsUnsatCoreFile};
        }

        // TODO: build Typecheckunits here?
        // Map<Integer, TypecheckUnit> solutionSlots = new HashMap<>();

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

    // Sample satisfying output format:
    /* @formatter:off // this is for eclipse formatter */
    /*
    sat
    (model
      (define-fun |338-BOT| () Bool
        false)
      (define-fun |509-TOP| () Bool
        false)
      (define-fun |750-m| () Int
        (- 9))
      (define-fun |355-s| () Int
        0)
      (define-fun |790-PREFIX| () Int
        0)
    )
    */
    /* @formatter:on // this is for eclipse formatter */

    // Sample unsat output format:
    /* @formatter:off // this is for eclipse formatter */
    /*
    unsat
    (SubtypeConstraint58 ArithmeticConstraint73 EqualityConstraint188 SubtypeConstraint553)
    */
    /* @formatter:on // this is for eclipse formatter */

    // parses the STD output from the z3 process and handles SAT and UNSAT
    // outputs
    private void parseStdOut(BufferedReader stdOut, List<String> results) {
        String line = "";

        boolean declarationLine = true;
        // each result line is "varName value"
        String resultsLine = "";

        boolean unsat = false;

        try {
            while ((line = stdOut.readLine()) != null) {
                line = line.trim();

                if (getUnsatCore) {
                    // UNSAT Cases ====================
                    if (line.contentEquals("unsat")) {
                        unsat = true;
                        continue;
                    }
                    if (unsat) {
                        if (line.startsWith("(")) {
                            line = line.substring(1); // remove open bracket
                        }
                        if (line.endsWith(")")) {
                            line = line.substring(0, line.length() - 1);
                        }

                        for (String constraintID : line.split(" ")) {
                            unsatConstraintIDs.add(constraintID);
                        }
                        continue;
                    }
                } else {
                    // SAT Cases =======================
                    // processing define-fun lines
                    if (declarationLine && line.startsWith("(define-fun")) {
                        declarationLine = false;

                        int firstBar = line.indexOf('|');
                        int lastBar = line.lastIndexOf('|');

                        assert firstBar != -1;
                        assert lastBar != -1;
                        assert firstBar < lastBar;
                        assert line.contains("Bool") || line.contains("Int");

                        // copy z3 variable name into results line
                        resultsLine += line.substring(firstBar + 1, lastBar);
                        continue;
                    }
                    // processing lines immediately following define-fun lines
                    if (!declarationLine) {
                        declarationLine = true;
                        String value = line.substring(0, line.lastIndexOf(')'));

                        if (value.contains("-")) { // negative number
                            // remove brackets surrounding negative numbers
                            value = value.substring(1, value.length() - 1);
                            // remove space between - and the number itself
                            value = String.join("", value.split(" "));
                        }

                        resultsLine += " " + value;
                        results.add(resultsLine);
                        resultsLine = "";
                        continue;
                    }
                }
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
