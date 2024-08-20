import java.util.Random;

public class UnitconMutator {
  static Random random = new Random();

  private static String getAscii() {
    char c = (char) (random.nextInt(95) + 32);
    return String.valueOf((c));
  }

  private static int getOperator() {
    return random.nextInt(3);
  }

  private static int getIndex(String seed) {
    if (seed.length() == 0) {
      return 0;
    }
    return random.nextInt(Integer.MAX_VALUE) % seed.length();
  }

  private static String remove(String seed, int index) {
    if (seed.length() - 1 <= index) {
      return seed.substring(0, seed.length());
    }
    return seed.substring(0, index) + seed.substring(index + 1);
  }

  private static String add(String seed, String newString, int index) {
    return seed.substring(0, index) + newString + seed.substring(index);
  }

  private static String replace(String seed, String newString, int index) {
    if (seed.length() - 1 <= index) {
      return seed.substring(0, seed.length()) + newString;
    }
    return seed.substring(0, index) + newString + seed.substring(index + 1);
  }

  private static String getMutation(String seed) {
    int index = getIndex(seed);
    String candidate = getAscii();
    switch(getOperator()) {
      case 0: // REMOVE
        return remove(seed, index);
      case 1: // ADD
        return add(seed, candidate, index);
      case 2: // REPLACE
        return replace(seed, candidate, index);
      default:
        System.err.println("Fail: UnitconMutator");
        return "";
    }
  }

  private static String[] mutateString(String seed, int numOfMutate) {
    String[] result = new String[numOfMutate + 1];
    result[0] = seed;
    for(int i =0; i < numOfMutate; i++) {
      result[i + 1] = getMutation(seed);
    }
    return result;
  }

  public static String[] mutateString(String[] seed, int numOfMutate) {
    boolean checkNull = false;
    for(int i = 0; i < seed.length; i++) {
      if (seed[i] == null) {
        checkNull = true;
      }
    }

    int length = seed.length * (numOfMutate + 1);
    if (checkNull) {
      length = length - numOfMutate;
    }

    String[] result = new String[length];
    int totalIndex = 0;

    for(int i = 0; i < seed.length; i++) {
      if (seed[i] == null) {
        result[totalIndex] = null;
        totalIndex = totalIndex + 1;
        continue;
      }
      String[] mList = mutateString(seed[i], numOfMutate);
      System.arraycopy(mList, 0, result, totalIndex, mList.length);
      totalIndex = totalIndex + mList.length;
    }
    return result;
  } 
}