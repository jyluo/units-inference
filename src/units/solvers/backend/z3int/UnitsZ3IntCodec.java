package units.solvers.backend.z3int;

import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.AnnotationMirror;
import org.checkerframework.javacutil.AnnotationUtils;
import checkers.inference.solver.backend.z3Int.Z3IntCodec;
import units.util.UnitsUtils;

public class UnitsZ3IntCodec implements Z3IntCodec {

    @Override
    public long encodeConstantAM(AnnotationMirror am) {
        System.out.println(" === ENCODING constant AM: " + am);
        
        if(AnnotationUtils.areSame(am, UnitsUtils.UNKNOWNUNITS)) {
            return 30L;
        }

        return 0L;
    }

    @Override
    public AnnotationMirror decodeNumeralValue(long numeralValue,
            ProcessingEnvironment processingEnv) {
        
        System.out.println(" === DECODING soln: " + numeralValue);
        
        return UnitsUtils.DIMENSIONLESS;
        
        // default return null for no solution.
    }
    //
    // private final int domainSize;
    //
    // private final Map<OntologyValue, Integer> ontologyValueEncodingMap;
    //
    // public UnitsZ3IntCodec() {
    // this.domainSize = OntologyValue.values.length - 2;
    //
    // // Check domain size limit.
    // // TODO: Extend supportability by using BitSet and BigInteger if needs.
    // if (domainSize > Integer.SIZE) {
    // ErrorReporter.errorAbort("Crruently Ontology Z3 BitVectorCodec implementation cannot support
    // domain size larger than " + Integer.SIZE);
    // }
    //
    // Map<OntologyValue, Integer> tempMap = new EnumMap<>(OntologyValue.class);
    // for (OntologyValue ontologyValue : OntologyValue.values) {
    // tempMap.put(ontologyValue, encodeOntologyValue(ontologyValue));
    // }
    // ontologyValueEncodingMap = Collections.unmodifiableMap(tempMap);
    // }
    //
    // @Override
    // public int getFixedBitVectorSize() {
    // return domainSize;
    // }
    //
    // @Override
    // public BigInteger encodeConstantAM(AnnotationMirror am) {
    // if (!AnnotationUtils.areSameIgnoringValues(am, OntologyUtils.ONTOLOGY)) {
    // return BigInteger.valueOf(-1);
    // }
    //
    // if (OntologyUtils.isOntologyTop(am)) {
    // return BigInteger.valueOf(0);
    // }
    //
    // OntologyValue[] values = OntologyUtils.getOntologyValues(am);
    // int encode = 0;
    // for (OntologyValue ontologyValue : values) {
    // encode |= ontologyValueEncodingMap.get(ontologyValue);
    // }
    // return BigInteger.valueOf(encode);
    // }
    //
    // @Override
    // public AnnotationMirror decodeNumeralValue(BigInteger numeralValue, ProcessingEnvironment
    // processingEnvironment) {
    // //TODO: change decoding to use BitSet, avoid using int.
    // int intNumberalValue = numeralValue.intValue();
    // Set<OntologyValue> ontologyValues = EnumSet.noneOf(OntologyValue.class);
    //
    // for (Entry<OntologyValue, Integer> entry : ontologyValueEncodingMap.entrySet()) {
    // int ontologyNumeralValue = entry.getValue();
    // OntologyValue ontologyValue = entry.getKey();
    // if ((ontologyNumeralValue & intNumberalValue) == ontologyNumeralValue) {
    // if (ontologyValue == OntologyValue.TOP && ontologyNumeralValue != intNumberalValue) {
    // continue;
    // }
    // ontologyValues.add(ontologyValue);
    // if (ontologyNumeralValue == intNumberalValue) {
    // break;
    // }
    // }
    // }
    //
    // return OntologyUtils.createOntologyAnnotationByValues(processingEnvironment,
    // ontologyValues.toArray(new OntologyValue[ontologyValues.size()]));
    // }
    //
    // protected int encodeOntologyValue(OntologyValue ontologyValue) {
    // int encode;
    //
    // if (ontologyValue == OntologyValue.TOP) {
    // return 0;
    // }
    //
    // if (ontologyValue == OntologyValue.BOTTOM) {
    // // Start from 0, then left-shift and accumulated by bit OR.
    // encode = 0;
    // for (int i = 0; i < domainSize; i ++) {
    // encode = encode << 1;
    // encode = encode | 1;
    // }
    // return encode;
    // }
    //
    // int oridnal = OntologyValue.singleRealValueToOrdinal.get(ontologyValue);
    // // Start from 1, then left-shift it to corresponding binary position.
    // encode = 1;
    // for (int i = 0; i < oridnal; i ++) {
    // encode = encode << 1;
    // }
    // return encode;
    // }
}
