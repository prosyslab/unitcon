public class Main {
  private Object getObject(int i) {
    if (i >= 10) {
      return null;
    }
    return new Object();
  }

  private String toString(int j) {
    Object o = getObject(j);
    return o.toString();
  }

  public void printString(int k) {
    String s = toString(k);
    System.out.println(s);
  }
}
