public class Main {
  public void errorMethod(Store s, int i, double j) {
    if (i > 30) {
      Object obj = s.getObj();
      if (obj != null) {
        Object log = s.getLog();
        String logStr = log.toString(); // NPE
      }
    }
  }
}