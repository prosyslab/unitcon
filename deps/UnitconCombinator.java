public class UnitconCombinator {
  public static String[] combinateString(String[] seed) {
    int countIgnore = 0;

    for (int i = 0; i < seed.length; i++) {
      if (seed[i] == null || seed[i] == "") {
        countIgnore++;
      }
    }

    int length = seed.length + (seed.length - countIgnore) * (seed.length - countIgnore);

    String[] result = new String[length];
    int totalIndex = 0;

    for (int i = 0; i < seed.length; i++) {
      for (int j = 0; j < seed.length; j++) {
        if (seed[i] == seed[j]) {
          result[totalIndex++] = seed[i];
        }
        if (seed[i] == null || seed[i] == "" || seed[j] == null || seed[j] == "") {
          continue;
        }
        result[totalIndex++] = seed[i] + seed[j];
      }
    }
    return result;
  }
}