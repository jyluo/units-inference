import units.qual.*;

class A {

    @m Integer o1;
    @m Integer o2;

    void test1() {
        Integer x = o1 + o2;
    }
    void test2() {
        Integer y = o1 + o2;
    }

    @m int x1;

    int test3() {
        return x1 + x1;
    }

    // issue: varslots being generated for auto unboxing... figure out why
    // try without any annotations on stubs
    // 
    // add getter of arithmetic slots based on location, saves another invocation of tree traversal
    // store component slots in arithmetic slot?? -- not safe for now for constant resolution
    // would be good if constants always resolved before
    // 

}