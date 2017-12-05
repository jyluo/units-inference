package units.util;

import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.util.Elements;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.ErrorReporter;
import units.qual.Dimensionless;
import units.qual.PolyUnit;
import units.qual.UnitsBottom;
import units.qual.UnknownUnits;
import units.qual.m;
import units.qual.s;

public class UnitsUtils {
    private static UnitsUtils singletonInstance;

    public static AnnotationMirror POLYUNIT;
    public static AnnotationMirror UNKNOWNUNITS;
    public static AnnotationMirror DIMENSIONLESS;
    public static AnnotationMirror BOTTOM;

    public static AnnotationMirror METER;
    public static AnnotationMirror SECOND;

    private UnitsUtils(ProcessingEnvironment processingEnv, Elements elements) {
        POLYUNIT = AnnotationBuilder.fromClass(elements, PolyUnit.class);
        UNKNOWNUNITS = AnnotationBuilder.fromClass(elements, UnknownUnits.class);
        DIMENSIONLESS = AnnotationBuilder.fromClass(elements, Dimensionless.class);
        BOTTOM = AnnotationBuilder.fromClass(elements, UnitsBottom.class);

        METER = AnnotationBuilder.fromClass(elements, m.class);
        SECOND = AnnotationBuilder.fromClass(elements, s.class);
    }

    public static UnitsUtils getInstance(ProcessingEnvironment processingEnv, Elements elements) {
        if (singletonInstance == null) {
            singletonInstance = new UnitsUtils(processingEnv, elements);
        }
        return singletonInstance;
    }

    public static UnitsUtils getInstance() {
        if (singletonInstance == null) {
            ErrorReporter.errorAbort("getInstance() called without initializing UnitsUtils.");
        }
        return singletonInstance;
    }

    //
    // public static OntologyValue determineOntologyValue(TypeMirror type) {
    // if (TypesUtils.isDeclaredOfName(type, "java.util.LinkedList")
    // || TypesUtils.isDeclaredOfName(type, "java.util.ArrayList")
    // || type.getKind().equals(TypeKind.ARRAY)) {
    // return OntologyValue.SEQUENCE;
    // }
    // // cannot determine OntologyValue by the given type
    // return OntologyValue.TOP;
    // }
    //
    // public static boolean isOntologyTop(AnnotationMirror type) {
    // if (!AnnotationUtils.areSameIgnoringValues(ONTOLOGY, type)) {
    // return false;
    // }
    //
    // OntologyValue[] values = getOntologyValues(type);
    // for (OntologyValue value : values) {
    // if (value == OntologyValue.TOP) {
    // return true;
    // }
    // }
    //
    // return false;
    // }
    //
    // public static AnnotationMirror createOntologyAnnotationByValues(ProcessingEnvironment
    // processingEnv,
    // OntologyValue... values) {
    // validateOntologyValues(values);
    // AnnotationBuilder builder = new AnnotationBuilder(processingEnv, Ontology.class);
    // builder.setValue("values", values);
    // return builder.build();
    // }
    //
    // public static OntologyValue[] getOntologyValues(AnnotationMirror type) {
    // List<OntologyValue> ontologyValueList = AnnotationUtils.getElementValueEnumArray(type,
    // "values", OntologyValue.class, true);
    // return ontologyValueList.toArray(new OntologyValue[ontologyValueList.size()]);
    // }
    //
    // public static EnumSet<OntologyValue> lubOfOntologyValues(EnumSet<OntologyValue> valueSet1,
    // EnumSet<OntologyValue> valueSet2) {
    // EnumSet<OntologyValue> lub = EnumSet.noneOf(OntologyValue.class);
    //
    // for (OntologyValue value1 : valueSet1) {
    // if (value1 == OntologyValue.TOP) {
    // lub.clear();
    // break;
    // }
    // if (valueSet2.contains(value1)) {
    // lub.add(value1);
    // }
    // }
    //
    // if (lub.isEmpty()) {
    // lub.add(OntologyValue.TOP);
    // }
    //
    // return lub;
    // }
    //
    // /**
    // * check whether the passed values are validated as arguments of Ontology qualifier
    // * valid values should not be null, and contains at least one ontology value, and
    // * doesn't cotains null element inside the array.
    // * @param values the checking values
    // */
    // protected static void validateOntologyValues(OntologyValue... values) {
    // if (values == null || values.length < 1) {
    // ErrorReporter.errorAbort("ontology values are invalid: " + values);
    // }
    // for (OntologyValue value : values) {
    // if (value == null) {
    // ErrorReporter.errorAbort("ontology values are invalid: " + values);
    // }
    // }
    // }
}
