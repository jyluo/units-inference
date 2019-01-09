import units.qual.*;

/**
* @skip-test
*/

import java.util.Iterator;

// from ode4j

// class MyList<T> implements Iterable<T> {
class MyList<@Dimensionless T extends @Dimensionless Object> implements Iterable<T> {
    public MyList<T> next = this;
    public MyList<T> prev = this;
    final T o;

    public MyList(T obj) {
        this.o = obj;
    }

    @SuppressWarnings("unchecked")
    @Override
    public Iterator<T> iterator() {
        return new Iterator<T>() {
            // TODO: fix bug with this version, and with next() below:
            // final MyIterator<T> iter = new MyIterator<T>(MyList.this);
            final MyIterator iter = new MyIterator(MyList.this);

            @Override
            public boolean hasNext() {
                return iter.hasNext();
            }

            @Override
            public T next() {
                // return iter.next();
                return (T) iter.next();
            }

            @Override
            public void remove() {}
        };
    }
}

class MyIterator<T> {
    private MyList<T> pos;
    private MyList<T> n;
    private final MyList<T> head;
    MyIterator(MyList<T> head) {
        this.head = head;
        this.pos = head.next;
        this.n = pos.next;
    }
    boolean hasNext() {
        return pos != head;
    }
    T next() {
        T prevPos = pos.o;
        pos = n;
        n = n.next;
        return prevPos;
    }
}
