/* Adapted from https://hg.mozilla.org/mozilla-central/rev/2448a35540d2 */

import units.qual.*;

class MozillaTabsTray {

    private static final @pxPERs int SWIPE_CLOSE_VELOCITY = (@pxPERs int) 1000;   // pixels/sec

    private static final @pxPERin int GECKO_APP_SHELL_DPI = (@pxPERin int) 72; // pixels/inch
    private static final @px int VIEW_WIDTH = (@px int) 100; // pixels

    // velocities in pixels / sec
    public boolean onFling(Object mView, @pxPERs float velocityX, @pxPERs float velocityY) {

        if (velocityX / GECKO_APP_SHELL_DPI > SWIPE_CLOSE_VELOCITY) {
            float d = (velocityX > (@pxPERs int) 0 ? 1 : -1) * VIEW_WIDTH;    // pixels

            // pixels / (pixels / sec) == sec, expect argument.type.incompatible here
            animateTo(mView, (int)d, (int)(d/velocityX));
        }

        // pixels / v = ms
        // v = pixel / ms

        return false; 
    }


    private static final @inPERs int SWIPE_CLOSE_VELOCITY2 = (@inPERs int) 5;   // iches/sec

    private static final @px int SCROLL_X = (@px int) 5;  // pixels

    public boolean onFlingFixed(Object mView, @pxPERs float velocityX, @pxPERs float velocityY) {
        // velocityX is in pixels/sec. divide by pixels/inch to compare it with swipe velocity
        if (velocityX / GECKO_APP_SHELL_DPI > SWIPE_CLOSE_VELOCITY2) {
            // is this is a swipe, we want to continue the row moving at the swipe velocity
            float d = (velocityX > (@pxPERs int) 0 ? 1 : -1) * VIEW_WIDTH;

            float msPERs = (@ms float) 1000 / (@s float) 1;

            // convert the velocity (px/sec) to ms by taking the distance
            // multiply by 1000 to convert seconds to milliseconds
            animateTo(mView, (int)d, (int)((d + SCROLL_X)*msPERs/velocityX));
        }

        return false; 
    }

    // x is final position, in pixels
    // duration in milliseconds
    private void animateTo(final Object view, @px int x, @ms int duration) {
        // performs some animation
    }
}

