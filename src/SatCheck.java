import java.util.*;
import java.io.*;

public class SatCheck {
   public static void main(String[] argv) {
      try {
         BufferedReader in = new BufferedReader(new FileReader(argv[0]));

         System.out.println("Enter assignment: ");
         BufferedReader stdin = new BufferedReader(new InputStreamReader(System.in));
         String first = stdin.readLine();

         String[] lits = first.split(" ");
         HashSet<Integer> h1 = new HashSet<Integer>();
         for(int i = 0; i < lits.length; i++) {
            Integer j = Integer.parseInt(lits[i]);
            if(j != 0) {
               h1.add(j);
            }
         }

         while(true) {
            String line = in.readLine();

            if(line == null) {
               break;
            }

            line = line.trim();

            if(line.startsWith("c") || line.startsWith("p")) {
               continue;
            }

            String[] literals = line.trim().split(" ");
            boolean bad = true;
            for(int i = 0; i < literals.length; i++) {
               Integer j = Integer.parseInt(literals[i]);
               if(j == 0) {
                  continue;
               }

               if(h1.contains(j)) {
                  bad = false;
                  break;
               }
            }
            if(bad) {
               System.err.println("NOT VALID");
               break;
            }
         }

         in.close();
         stdin.close();
      } catch(Exception ex) {
         ex.printStackTrace();
      }
   }
}
