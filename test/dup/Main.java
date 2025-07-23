public class Main {
  public void checkDup(Dup dup, int i) {
    Object o = dup.getObject(i);
    String s = o.toString();
    System.out.println(s);
  }
}
