package units;

import java.util.List;
import java.util.Map;
import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.AnnotationValue;
import javax.lang.model.element.VariableElement;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.util.DefaultAnnotationFormatter;
import units.representation.UnitsRepresentationUtils;

public class UnitsAnnotationFormatter extends DefaultAnnotationFormatter {

    public UnitsAnnotationFormatter(BaseTypeChecker checker) {}

    @Override
    public String formatAnnotationMirror(AnnotationMirror anno) {
        
        System.out.println(" === formatting: " + anno.toString());

        // Substitutes known annotations with their aliases so that we print them as their more
        // understandable alias annotations
        Map<AnnotationMirror, AnnotationMirror> unitsAliasMap =
                UnitsRepresentationUtils.getInstance().getUnitsAliasMapSwapped();
        for (AnnotationMirror key : unitsAliasMap.keySet()) {
            
            if (anno.toString().startsWith("@units.qual.UnitsInternal(unknownUnits=true")) {
                System.out.println(" === comparing to: " + key.toString());
            }

            if (anno.toString().contentEquals(key.toString())) {
                return super.formatAnnotationMirror(unitsAliasMap.get(key));
            }
        }
        return super.formatAnnotationMirror(anno);
    }

    // Same as superclass implementation except that we recursively format nested annotations
    @Override
    protected void formatAnnotationMirrorArg(AnnotationValue av, StringBuilder sb) {
        Object val = av.getValue();

        if (List.class.isAssignableFrom(val.getClass())) {
            @SuppressWarnings("unchecked")
            List<AnnotationValue> valList = (List<AnnotationValue>) val;
            if (valList.size() == 1) {
                formatAnnotationMirrorArg(valList.get(0), sb);
            } else {
                sb.append('{');
                boolean notfirst = false;
                for (AnnotationValue nav : valList) {
                    if (notfirst) {
                        sb.append(", ");
                    }
                    notfirst = true;
                    formatAnnotationMirrorArg(nav, sb);
                }
                sb.append('}');
            }
        } else if (VariableElement.class.isAssignableFrom(val.getClass())) {
            VariableElement ve = (VariableElement) val;
            sb.append(ve.getEnclosingElement().getSimpleName() + "." + ve.getSimpleName());
        } else if (val instanceof AnnotationMirror) {
            // this is the new case added
            // if the argument is an AnnotationMirror, then recursively format the AnnotationMirror
            formatAnnotationMirror((AnnotationMirror) val, sb);
        } else {
            sb.append(av.toString());
        }
    }
}
