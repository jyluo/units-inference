import units.qual.*;
import units.UnitsTools;

class Println {

    void Main() {
        @ns long start = (@ns long) 0L;

        // @ms long fail = System.nanoTime();

        System.out.println("Computation time: " + (System.nanoTime() - start) / 1e9 + " sec");
    }
}