import lib.FlowNetwork;
import lib.FordFulkerson;

public class fofu {
    static FordFulkerson maxflow;

    public static long doTest(FlowNetwork G) {
      int V_size = G.V();
      int E_size = G.E();

      System.gc();

      long startTime = System.currentTimeMillis();
      maxflow = new FordFulkerson(G, 0, V_size - 1);
      long endTime   = System.currentTimeMillis();
      return (endTime - startTime);
    }


    // test client that reads input network, solves max flow, and prints results
    public static void main(String[] args) throws Exception {
    	if (args.length > 2 || args.length < 1) {
    		System.out.println("Usage: [<WARMUP-PATH>] <GRAPH-PATH>");
    	}
    	else {
          int i=0;
          
          if (args.length == 2) {
            // Warm up
            FlowNetwork G = new FlowNetwork(args[i]);
            doTest(G);
            doTest(G);
            doTest(G);
            doTest(G);
            i++;
          }

	        FlowNetwork G = new FlowNetwork(args[i]);
	        long time = doTest(G);
          System.out.format("@@@time: %d ms\n", time);
          System.out.format("[Input (V E): %d %d]\n", G.V(), G.E());
          System.out.format("@@@max-flow: %d\n", (int)maxflow.value());
          System.out.format("outer_c: %d\n\tinner_c: %d\n", maxflow.outer_c, maxflow.inner_c);
	        
// 	        if (V_size > 0 && V_size <= 10000) {
// 	          
// 	          G = new FlowNetwork(args[1]);
//             int V_size = G.V();
//             int E_size = G.E();
// 
// 	          System.gc();
// 
// 	        	long startTime = System.currentTimeMillis();
// 	        	
// 	        	FordFulkerson maxflow = new FordFulkerson(G, 0, V_size - 1);
// 	        
// 	        	long endTime   = System.currentTimeMillis();
// 	        
// 	        	System.out.format("@@@ Execution Time: %d milliseconds\n", endTime - startTime);
// 	        	System.out.format("\t[Input (V E): %d %d]\n", V_size, E_size);
// 	        	System.out.format("\t=> Maximum flow value: %d\n", (int)maxflow.value());
// 	        	System.out.format("\touter_c: %d\n\tinner_c: %d\n", maxflow.outer_c, maxflow.inner_c);
// 	        }
// 	        else {
// 	        	System.out.println("Input Graph is invalid");	        	
// 	        }
    	}
    }

}
