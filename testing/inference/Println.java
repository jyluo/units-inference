import units.qual.*;

class Println {

    void test() {
        @ns long start = (@ns long) 0L;

        // @ms long fail = System.nanoTime();

        System.out.println("Computation time: " + (System.nanoTime() - start) / 1e9 + " sec");
    }
}
