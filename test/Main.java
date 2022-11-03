class State {
    public void execute() {

    }
}

class Obj {
    public State getState(int i) {
        if (i == 0)
                return new State();
       else
                return null;
    }
}

public class Main {
    public void f(Obj o, int i) {
        State s = o.getState(i);
        s.execute(); // NPE
     }
 }

