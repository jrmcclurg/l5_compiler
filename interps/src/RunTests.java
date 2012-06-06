import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Vector;

public class RunTests {
   static final String interpsLocation = "/home/jrmcclurg/svn/compilers/interps/";
   static final String testLocation = interpsLocation+"tests/";
   static boolean printAll = false;
   
   public static void main(String[] argv) {
      try {
         int num = Integer.parseInt(argv[0]);
         String compilerLocation = argv[1];
         
         if(argv.length > 2 && argv[2].equals("-all")) {
            printAll = true;
         }
         
         File compilerFiles[] = new File[num];
         for(int j = num, i = 1; i <= num; i++, j--) {
            compilerFiles[i-1] = new File(compilerLocation, "L"+j+"c");
            System.out.println("Using compiler: "+compilerFiles[i-1].getAbsolutePath());
         }
         
         Vector<File> tests = collectAllTests(testLocation, num, new Vector<File>());
         int numPassed = 0;
         long binaryTime = 0;
         long interpTime = 0;
         for(int i = 0; i < tests.size(); i++) {
            File f = tests.elementAt(i);

            System.err.printf("Testing %d/%d : %s ... ",(i+1),tests.size(),f.getAbsolutePath());
            System.err.flush();
            
            String interpCommand = interpsLocation+"L"+num+" "+f.getAbsolutePath();

            String binaryPath = interpsLocation+"tempBinary";
            for(int j = 0; j < compilerFiles.length; j++) {
               String command = "";
               command += compilerFiles[j].getAbsolutePath();
               if(j == 0) {
                  String temp = f.getAbsolutePath();
                  //temp = "This is a test";
                  //temp = temp.replaceAll(" ", "\\\\ ");
                  command += " " + temp;
                  //System.out.println(temp);
                  //System.exit(1);
                  
               } else {
                  command += " " + interpsLocation + "temp." + (j-1);
               }
               
               command += " -o ";
               
               if(j == compilerFiles.length-1) {
                  command += binaryPath;
               } else {
                  command += interpsLocation + "temp." + j;
               }
               //System.out.println("Command: '"+command+"'\n");
               Process p = Runtime.getRuntime().exec(command);
               p.waitFor();
            }
            //command += " -o "+interpsLocation+"testCompiled";
            
            Result result1 = runAndGetOutput(binaryPath);
            Result result2 = runAndGetOutput(interpCommand);
            
            boolean equal = result1.result.equals(result2.result);
            
            if(equal) {
               ++numPassed;
            }
            
            binaryTime += result1.time;
            interpTime += result2.time;
            
            if(!equal || printAll){
               System.out.printf("%4d/%4d ... ",(i+1),tests.size());
               System.out.print(equal ? "passed" : "failed");
               System.out.printf(" : %3d ms (%4d ms) : %4d / %4d = %3.2f : ", result1.time, result2.time, numPassed, (i+1), (numPassed/(float)(i+1)*100.0));
               System.out.println(f.getAbsolutePath());
            }
            //System.out.println(result);
            //Runtime.getRuntime().exec("./a.out");
            //break; // XXX

            System.err.println("done.");
            System.err.flush();
         }
         float percentage = (float)numPassed/(float)tests.size()*100.0f;
         System.out.printf("Num passed: %d out of %d (%.2f%%)\n",numPassed,tests.size(),percentage);
         System.out.printf("Timing:     %d ms (%d ms), avg: %.2f (%.2f)\n",binaryTime,interpTime,(binaryTime/(float)tests.size()),(interpTime/(float)tests.size()));
      } catch(Exception ex) {
         ex.printStackTrace();
         System.err.println("Usage:");
         System.err.println("   java RunTests num path [-all]");
         System.err.println("   (where you want to run the Lnum in path)");
      }
   }
   
   public static Result runAndGetOutput(String cmd) throws IOException, InterruptedException {
      String result = "";
      long start = System.currentTimeMillis();
      Process p = Runtime.getRuntime().exec(cmd);
      p.waitFor();
      long end = System.currentTimeMillis();
      BufferedReader in = new BufferedReader(new InputStreamReader(p.getInputStream()));
      while(true) {
         String line = in.readLine();
         if(line == null) break;
         result += line + "\n";
      }
      return new Result(result, end-start);
   }
   
   public static Vector<File> collectAllTests(String dir, int num, Vector<File> files) {
      Vector<File> result = new Vector<File>(files);
      File d = new File(dir);
      File list[] = d.listFiles();
      for(int i = 0; i < list.length; i++) {
         File f = list[i];
         if(f.isDirectory()) {
            result.addAll(collectAllTests(f.getAbsolutePath(),num,files));
         } else if(f.getName().endsWith(".L"+num) && !f.isHidden()) {
            result.add(f);
         }
      }
      return result;
   }
}
