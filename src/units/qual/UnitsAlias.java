package units.qual;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Meta-annotation for declaring a compound unit in terms of its normalized representation.
 *
 * @see {@link UnitsRep}
 * @checker_framework.manual #units-checker Units Checker
 */
@Documented
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.ANNOTATION_TYPE})
public @interface UnitsAlias {

    boolean top() default false;

    boolean bot() default false;

    int p() default 0;

    BUC[] bu() default {};
}
