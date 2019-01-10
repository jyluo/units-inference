package backend.z3smt;

import checkers.inference.model.ArithmeticConstraint;
import checkers.inference.model.ArithmeticConstraint.ArithmeticOperationKind;
import checkers.inference.model.Constraint;
import checkers.inference.model.Slot;
import checkers.inference.solver.backend.Solver;
import checkers.inference.solver.frontend.Lattice;
import checkers.inference.solver.util.SolverArg;
import checkers.inference.solver.util.SolverEnvironment;
import checkers.inference.solver.util.Statistics;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import javax.lang.model.element.AnnotationMirror;

// TODO: make this an abstract class with common features
public abstract class Z3SmtSolver<SlotEncodingT, ConstraintEncodingT, SlotSolutionT>
        extends Solver<Z3SmtFormatTranslator<SlotEncodingT, ConstraintEncodingT, SlotSolutionT>> {

    public enum Z3SolverEngineArg implements SolverArg {
        /** command line option to use optimizing mode or not */
        optimizingMode
    }

    protected final Context ctx;

    protected static final String z3Program = "z3";
    protected static final String smtExtension = ".smt";

    // Used in non-optimizing mode to find unsat constraints
    // Note that the z3 terms across the base units share the same unsat core
    // constraint name. As long as one of the base units with this constraint name
    // is unsat, then the whole constraint set is unsat.
    protected final Map<String, Constraint> serializedConstraints = new HashMap<>();
    protected final List<String> unsatConstraintIDs = new ArrayList<>();

    // file is written at projectRootFolder/xxx.smt
    protected static final String pathToProject =
            new File(new File("").getAbsolutePath()).toString();
    protected static final String constraintsFilePrefix = "/z3Constraints-";
    protected static final String constraintsUnsatCoreFilePrefix = "/z3ConstraintsUnsatCore-";
    protected static final String constraintsStatsFilePrefix = "/z3ConstraintsGlob-";

    // protected static final String constraintsFile = pathToProject +
    // "/z3Constraints.smt";
    // protected static final String constraintsUnsatCoreFile =
    // pathToProject + "/z3ConstraintsUnsatCore.smt";
    // protected static final String constraintsStatsFile = pathToProject +
    // "/z3ConstraintsGlob.smt";

    // timing statistics variables
    protected long serializationStart;
    protected long serializationEnd;
    protected long solvingStart;
    protected long solvingEnd;

    protected enum Mode {
        SatMode,
        GetUnsatCore,
        OptimizingMode,
    }

    /** Z3 solver's encoding mode */
    protected Mode mode = Mode.SatMode;

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

        // serialize based on user choice of running in optimizing or non-optimizing
        // mode
        if (solverEnvironment.getBoolArg(Z3SolverEngineArg.optimizingMode)) {
            mode = Mode.OptimizingMode;
            System.err.println(" === running in optimizing mode ! ===");
        }

        serializeSMTFileContents();

        solvingStart = System.currentTimeMillis();
        // in Units, if the status is SAT then there must be output in the model
        Set<String> results = runZ3Solver();
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
                            slots, results, solverEnvironment.processingEnvironment);
        } else {
            System.err.println("\n\n!!! The set of constraints is unsatisfiable! !!!");
            result = null;
        }

        return result;
    }

    @Override
    public Collection<Constraint> explainUnsatisfiable() {
        mode = Mode.GetUnsatCore;

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

    protected String z3Assert(Expr clause) {
        return "(assert " + clause.toString() + ")" + System.lineSeparator();
    }

    protected String z3UnsatCoreAssert(Expr clause, String constraintName) {
        return "(assert (! "
                + clause.toString()
                + " :named "
                + constraintName
                + "))"
                + System.lineSeparator();
    }

    protected String z3SoftAssert(Expr clause, int weight) {
        return "(assert-soft "
                + clause.toString()
                + " :weight "
                + weight
                + ")"
                + System.lineSeparator();
    }

    protected String z3SoftAssert(Expr clause) {
        return z3SoftAssert(clause, 1);
    }

    protected abstract void serializeSMTFileContents();

    protected abstract void writeConstraintsToSMTFile();

    protected abstract void encodeAllSlots();

    protected abstract Set<String> runZ3Solver();

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
    protected void parseStdOut(BufferedReader stdOut, List<String> results) {
        String line = "";

        boolean declarationLine = true;
        // each result line is "varName value"
        String resultsLine = "";

        boolean unsat = false;

        try {
            while ((line = stdOut.readLine()) != null) {
                line = line.trim();

                if (mode == Mode.GetUnsatCore) {
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
