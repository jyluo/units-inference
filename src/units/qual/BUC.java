package units.qual;

import java.lang.annotation.Annotation;
import java.lang.annotation.Documented;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;

/** Base unit component */
@Documented
@Retention(RetentionPolicy.RUNTIME)
public @interface BUC {
    Class<? extends Annotation> unit();

    int exponent() default 0;
}
