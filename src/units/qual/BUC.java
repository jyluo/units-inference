package units.qual;

import java.lang.annotation.Documented;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;

/** Base unit component */
@Documented
@Retention(RetentionPolicy.RUNTIME)
public @interface BUC {
    // TODO: use Class<? extends Annotation> when annotation inserter can properly
    // insert class literals as values in annotations
    String unit();

    int exponent() default 0;
}
