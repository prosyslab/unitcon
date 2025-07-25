public class Main {
  public void errorMethod(Constructor c) {
    Object o = c.getObj();
    o.toString(); // NPE
  }
}
