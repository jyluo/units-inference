package backend.z3smt;

import checkers.inference.InferenceMain;
import checkers.inference.model.ArithmeticConstraint;
import checkers.inference.model.ArithmeticConstraint.ArithmeticOperationKind;
import checkers.inference.model.ComparableConstraint;
import checkers.inference.model.Constraint;
import checkers.inference.model.Slot;
import checkers.inference.model.SubtypeConstraint;
import checkers.inference.model.VariableSlot;
import checkers.inference.solver.backend.Solver;
import checkers.inference.solver.frontend.Lattice;
import checkers.inference.solver.util.SolverEnvironment;
import checkers.inference.solver.util.StatisticRecorder;
import checkers.inference.solver.util.StatisticRecorder.StatisticKey;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import javax.lang.model.element.AnnotationMirror;

public class Z3SmtSolver<SlotEncodingT, SlotSolutionT>
        extends Solver<Z3SmtFormatTranslator<SlotEncodingT, SlotSolutionT>> {

    protected final Context ctx;
    protected com.microsoft.z3.Optimize solver;
    protected StringBuffer smtFileContents;

    protected final String z3Program = "z3";
    protected boolean optimizingMode;
    protected boolean getUnsatCore;

    // used in non-optimizing mode to find unsat constraints
    protected final Map<String, Constraint> serializedConstraints = new HashMap<>();
    protected final List<String> unsatConstraintIDs = new ArrayList<>();

    // file is written at projectRootFolder/constraints.smt
    protected final String pathToProject = new File(new File("").getAbsolutePath()).toString();
    protected final String constraintsFile = pathToProject + "/z3Constraints.smt";
    protected final String constraintsStatsFile = pathToProject + "/z3ConstraintStats.smt";

    // timing statistics variables
    protected long serializationStart;
    protected long serializationEnd;
    protected long solvingStart;
    protected long solvingEnd;

    public Z3SmtSolver(
            SolverEnvironment solverEnvironment,
            Collection<Slot> slots,
            Collection<Constraint> constraints,
            Z3SmtFormatTranslator<SlotEncodingT, SlotSolutionT> z3SmtFormatTranslator,
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
    @SuppressWarnings("unused")
    @Override
    public Map<Integer, AnnotationMirror> solve() {
        Map<Integer, AnnotationMirror> result;

        // Runtime.getRuntime().gc(); // trigger garbage collector

        // first time serialize and run in optimizing mode
        optimizingMode = true;
        getUnsatCore = false;

        System.out.println("Now encoding with soft constraints");
        serializeSMTFileContents();

        System.out.println("Starting the solving");
        solvingStart = System.currentTimeMillis();
        // in Units, if the status is SAT then there must be output in the model
        List<String> results = runZ3Solver();
        solvingEnd = System.currentTimeMillis();
        System.out.println("Solving Complete");

        // add -solverArgs collectStatistic to print?
        StatisticRecorder.record(
                StatisticKey.SAT_SERIALIZATION_TIME, serializationEnd - serializationStart);
        StatisticRecorder.record(StatisticKey.SAT_SOLVING_TIME, solvingEnd - solvingStart);

        System.out.println(
                "SMT Serialization Time (millisec): " + (serializationEnd - serializationStart));
        System.out.println("SMT Solving Time (millisec): " + (solvingEnd - solvingStart));

        // Debug use, finds out number of calls to each instrumented method
        System.out.println("=== Arithmetic Constraints Printout ===");
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
            System.out.println(
                    " Made arithmetic "
                            + kind.getSymbol()
                            + " constraint: "
                            + arithmeticConstraintCounters.get(kind));
        }

        System.out.println("=== Comparison Constraints Printout ===");
        int comparableConstraints = 0;
        for (Constraint constraint : constraints) {
            if (constraint instanceof ComparableConstraint) {
                comparableConstraints++;
            }
        }
        System.out.println(" Made comparison constraint: " + comparableConstraints);

        // System.out.println("=== Solutions: ===");
        // for (String r : results) {
        // System.out.println(r);
        // }

        if (!results.isEmpty()) {
            result =
                    formatTranslator.decodeSolution(
                            results, solverEnvironment.processingEnvironment);
        } else {
            System.out.println("\n\n!!! The set of constraints is unsatisfiable! !!!");

            optimizingMode = false;
            getUnsatCore = true;

            System.out.println("Now encoding for unsat core dump.");
            serializeSMTFileContents();

            System.out.println("Starting the solving");
            solvingStart = System.currentTimeMillis();
            // in Units, if the status is SAT then there must be output in the model
            results = runZ3Solver();
            solvingEnd = System.currentTimeMillis();
            System.out.println("Solving Complete");

            System.out.println(
                    "SMT UNSAT Serialization Time (millisec): "
                            + (serializationEnd - serializationStart));
            System.out.println("SMT UNSAT Solving Time (millisec): " + (solvingEnd - solvingStart));

            System.out.println();
            System.out.println(
                    "Unsatisfiable constraints: " + String.join(" ", unsatConstraintIDs));
            System.out.println();

            for (String constraintID : unsatConstraintIDs) {
                Constraint c = serializedConstraints.get(constraintID);
                System.out.println(constraintID + " :");
                System.out.println(c);
                System.out.println(c.getLocation());
                System.out.println();
            }

            result = new HashMap<>();
        }

        return result;
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

        System.out.println("Encoding constraints done!");

        smtFileContents.append("(check-sat)\n");
        smtFileContents.append("(get-model)\n");
        if (!optimizingMode && getUnsatCore) {
            smtFileContents.append("(get-unsat-core)\n");
        }

        System.out.println("Writing constraints to file: " + constraintsFile);

        writeConstraintsToSMTFile();
    }

    private void writeConstraintsToSMTFile() {
        String fileContents = smtFileContents.toString();

        try {
            FileWriter fw = new FileWriter(constraintsFile, false);
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter pw = new PrintWriter(bw);
            pw.write(fileContents);
            pw.close();
        } catch (Exception e) {
            e.printStackTrace();
        }

        // write a copy in append mode to stats file for later bulk analysis
        try {
            FileWriter fw = new FileWriter(constraintsStatsFile, true);
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter pw = new PrintWriter(bw);
            pw.write(fileContents);
            pw.close();
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    protected void encodeAllSlots() {
        for (Slot slot : slots) {
            if (slot instanceof VariableSlot) {
                VariableSlot varSlot = (VariableSlot) slot;

                solver.Assert(formatTranslator.encodeSlotWellformnessConstraint(varSlot));

                if (optimizingMode) {
                    // empty string means no optimization group
                    solver.AssertSoft(
                            formatTranslator.encodeSlotPreferenceConstraint(varSlot), 1, "");
                }
            }
        }

        // solver.toString() also includes "(check-sat)" as the last line, remove it
        String slotDefinitionsAndConstraints = solver.toString();
        int truncateIndex = slotDefinitionsAndConstraints.lastIndexOf("(check-sat)");
        assert truncateIndex != -1;

        smtFileContents.append(slotDefinitionsAndConstraints.substring(0, truncateIndex));

        // debug use:
        // Write Slots to file
        String writePath = pathToProject + "/slots.smt";
        try {
            FileWriter fw = new FileWriter(writePath, false); // appends to slots.smt
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter pw = new PrintWriter(bw);
            pw.write(solver.toString());
            pw.close();
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    @Override
    protected void encodeAllConstraints() {
        int total = constraints.size();

        int current = 1;
        List<String> constraintClauses = new ArrayList<>();

        for (Constraint constraint : constraints) {
            // System.out.println("Getting next item.");

            // System.out.println(
            // " Serializing Constraint " + current + " / " + total + " : " + constraint);

            // if (current % 100 == 0) {
            // System.out.println("=== Running GC ===");
            // Runtime.getRuntime().gc(); // trigger garbage collector
            // }

            BoolExpr serializedConstraint = constraint.serialize(formatTranslator);

            // System.out.println(" Constraint serialized. ");

            if (serializedConstraint == null) {
                // TODO: Should error abort if unsupported constraint detected.
                // Currently warning is a workaround for making ontology working, as in some
                // cases
                // existential constraints generated.
                // Should investigate on this, and change this to ErrorAbort when eliminated
                // unsupported constraints.
                System.out.println(
                        "Unsupported constraint detected! Constraint type: "
                                + constraint.getClass().getSimpleName());
                current++;
                continue;
            }

            // System.out.println(" Constraint \n" + serializedConstraint
            // + "\n simplified :\n " + serializedConstraint.simplify());

            Expr simplifiedConstraint = serializedConstraint.simplify();

            if (simplifiedConstraint.isTrue()) {
                // This only works if the BoolExpr is directly the value Z3True. Still a good
                // filter, but doesn't filter enough.
                // EG: (and (= false false) (= false false) (= 0 0) (= 0 0) (= 0 0))
                // Skip tautology.
                // System.out.println(" simplified to tautology.");
                current++;
                continue;
            }

            String clause = simplifiedConstraint.toString();

            if (!optimizingMode && getUnsatCore) {
                // add assertions with names, for unsat core dump
                String constraintName = constraint.getClass().getSimpleName() + current;

                smtFileContents.append("(assert (! ");
                smtFileContents.append(clause);
                smtFileContents.append(" :named " + constraintName + "))\n");

                serializedConstraints.put(constraintName, constraint);
            } else {
                smtFileContents.append("(assert ");
                smtFileContents.append(clause);
                smtFileContents.append(")\n");
            }

            constraintClauses.add(simplifiedConstraint.toString());

            // generate a soft constraint that we prefer equality for subtype
            if (optimizingMode && constraint instanceof SubtypeConstraint) {
                SubtypeConstraint stc = (SubtypeConstraint) constraint;

                Constraint eqc =
                        InferenceMain.getInstance()
                                .getConstraintManager()
                                .createEqualityConstraint(stc.getSubtype(), stc.getSupertype());

                Expr simplifiedEQC = eqc.serialize(formatTranslator).simplify();

                if (!simplifiedEQC.isTrue()) {
                    smtFileContents.append("(assert-soft ");
                    smtFileContents.append(simplifiedEQC);
                    smtFileContents.append(" :weight 1)\n");
                }
            }

            // generate soft constraint for comparisons that their args are equal
            if (optimizingMode && constraint instanceof ComparableConstraint) {
                ComparableConstraint cc = (ComparableConstraint) constraint;

                Constraint eqc =
                        InferenceMain.getInstance()
                                .getConstraintManager()
                                .createEqualityConstraint(cc.getFirst(), cc.getSecond());

                Expr simplifiedEQC = eqc.serialize(formatTranslator).simplify();

                if (!simplifiedEQC.isTrue()) {
                    smtFileContents.append("(assert-soft ");
                    smtFileContents.append(simplifiedEQC);
                    smtFileContents.append(" :weight 1)\n");
                }
            }

            current++;
            // // System.out.println(" Added constraint. HasNext? " + iter.hasNext());
        }

        // debug use
        // Write Slots to file
        String writePath = pathToProject + "/constraints.smt";
        try {
            FileWriter fw = new FileWriter(writePath, false); // appends to constraints.smt
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter pw = new PrintWriter(bw);

            for (String clause : constraintClauses) {
                pw.write("(assert ");
                pw.write(clause);
                pw.write(")\n");
            }

            pw.close();
        } catch (Exception e) {
            e.printStackTrace();
        }
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
    (error "line yyy column 10: model is not available")
    (SubtypeConstraint58 ArithmeticConstraint73 EqualityConstraint188 SubtypeConstraint553)
    */
    /* @formatter:on // this is for eclipse formatter */

    // A thread which handles the STD output from the z3 process, parsing SAT and UNSAT outputs
    private class Z3OutputHandler extends Thread {
        private final Process z3Process;
        private final List<String> results;

        public Z3OutputHandler(Process z3Process, List<String> results) {
            this.z3Process = z3Process;
            this.results = results;
        }

        @Override
        public void run() {
            String line = "";
            BufferedReader stdInput =
                    new BufferedReader(new InputStreamReader(z3Process.getInputStream()));

            boolean declarationLine = true;
            // each result line is "varName value"
            String resultsLine = "";

            boolean unsat = false;

            try {
                while ((line = stdInput.readLine()) != null) {
                    line = line.trim();

                    // UNSAT Cases ====================
                    if (line.contentEquals("unsat")) {
                        unsat = true;
                        // skip over output line for get-model
                        stdInput.readLine();
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
                        ;
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
                    // process no-unsat core line
                    // example output: (error "line 35892 column 15: unsat core is not available")
                    if (line.contains("unsat core is not available")) {
                        continue;
                    }
                }
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }

    private List<String> runZ3Solver() {
        // TODO: add z3 stats?
        String command = z3Program + " " + constraintsFile;

        // TODO: build TCU here?
        // Map<Integer, TypecheckUnit> solutionSlots = new HashMap<>();

        // stores results from z3 program output
        final List<String> results = new ArrayList<>();

        // spin up subprocess to execute z3
        try {
            System.out.println("Running program: " + command);
            System.out.flush();

            final Process z3Process = Runtime.getRuntime().exec(command);

            // spin up 2 threads at the same time to analyze z3 std output and catch std errors
            Thread handleZ3Output = new Z3OutputHandler(z3Process, results);
            handleZ3Output.start();

            Thread handleZ3Error =
                    new Thread() {
                        @Override
                        public void run() {
                            String errorLine = "";
                            StringBuilder sb = new StringBuilder();
                            BufferedReader stdError =
                                    new BufferedReader(
                                            new InputStreamReader(z3Process.getErrorStream()));
                            try {
                                while ((errorLine = stdError.readLine()) != null) {
                                    sb.append(errorLine); // need + "\n" ?
                                }
                                System.err.println(sb.toString());
                            } catch (IOException e) {
                                e.printStackTrace();
                            }
                        }
                    };
            handleZ3Error.start();

            // wait for threads to die
            handleZ3Output.join();
            handleZ3Error.join();
            // tell Java's thread to wait for z3 process to finish
            int exitStatus = z3Process.waitFor();

            // TODO: handle exit status for z3 process crashes, out of memory, etc

        } catch (IOException e) {
            e.printStackTrace();
        } catch (InterruptedException e) {
            e.printStackTrace();
        }

        return results;
    }

    @Override
    public Collection<Constraint> explainUnsatisfiable() {
        // TODO in the future
        return null;
    }
}
