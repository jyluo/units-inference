package units;

import java.util.List;
import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.AnnotationValue;
import javax.lang.model.element.VariableElement;
import units.utils.UnitsRepresentationUtils;
import org.checkerframework.framework.util.DefaultAnnotationFormatter;

public class UnitsAnnotationFormatter extends DefaultAnnotationFormatter {

    /** reference to the units representation utilities library */
    protected UnitsRepresentationUtils unitsRepUtils;

    public UnitsAnnotationFormatter() {}

    public void postInit(UnitsRepresentationUtils unitsRepUtils) {
        this.unitsRepUtils = unitsRepUtils;
    }

    @Override
    protected void formatAnnotationMirror(AnnotationMirror anno, StringBuilder sb) {
        super.formatAnnotationMirror(unitsRepUtils.getPrettyPrintUnit(anno), sb);
    }

    // Same as superclass implementation except that it also recursively formats nested annotations
    // this is needed to format the {@link units.qual.BUC} annotations
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
