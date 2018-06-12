import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.List;
import java.util.PriorityQueue;
import java.util.Stack;

import java.io.Writer;

class Algorithm
{
    String path;
    public Algorithm(String p)
    {
        path = p;
    }
    /// <summary>
    /// return true if ras2 subseteq ras1
    /// </summary>
    /// <param name="ras1"></param>
    /// <param name="ras2"></param>
    /// <returns></returns>
    public Boolean RASinRAS(RAS ras1, RAS ras2)
    {
        for (int i = 0; i < ras2.Safe.size(); i++)
        {
        	//Ahmed not sure if index of works
            int idx = ras1.States.indexOf(ras2.States.get(i));
            //Ahmed
            //Probably impossible
            if (idx == -1)
                return false;
            if ((ras2.Safe.get(i) == true) && (ras1.Safe.get(idx) == false))
                return false;
        }
        return true;
    }

    public Boolean RASinPolicies(List<RAS> policies, RAS ras)
    {
        for (int i = 0; i < policies.size(); i++)
        {
            if (RASinRAS(policies.get(i), ras))
                return true;
        }
        return false;
    }


    public List<RAS> AddRASToPolicies(List<RAS> policies, RAS ras)
    {
        for (int i = policies.size() - 1; i >= 0; i--)
        {
            if (RASinRAS(ras, policies.get(i)))
                policies.remove(i);
        }
        policies.add(ras);
        return policies;
    }

    public void WriteMaximalRAS(int pn, int numExplored, List<RAS> MaximalPolicies)
    {
    	try
    	{
	    	BufferedWriter writer = new BufferedWriter(new OutputStreamWriter
	        		(new FileOutputStream(path + "Maximal DAP" + pn + ".txt")));
	        if (numExplored == 1)
	        {
	            writer.write("linear");
	            writer.newLine();
	        }
	        else
	        {
	            writer.write(MaximalPolicies.size());
	            writer.newLine();
	            for (int i = 0; i < MaximalPolicies.size(); i++)
	            {
	                writer.write(i);
	                writer.newLine();
	                for (int itr = 0; itr < MaximalPolicies.get(i).States.size(); itr++)
	                {
	                    if (MaximalPolicies.get(i).Safe.get(itr))
	                    {
	                        writer.write(MaximalPolicies.get(i).States.get(itr));
	                        writer.newLine();
	                    }
	                }
	            }
	        }
	        writer.close();
    	}
    	catch(Exception e)
    	{
    		
    	}
    }
    
    // This function returns the linear policy with the maximum number of safe states
    public void SolvePNMax()
    {
    	/*RAS ras = new RAS();
        ras.p = 4;
        ras.r = 2;
        ras.t = 4;
        ras.m0 = new int[ras.p]; ras.m0[0] = 0; ras.m0[1] = 0; ras.m0[2] = 3; ras.m0[3] = 3;
        ras.C = new int[ras.p][ras.t];
        ras.C[0][0] = -1; ras.C[1][0] = 0; ras.C[2][0] = 1; ras.C[3][0] = 0;
        ras.C[0][1] = 0; ras.C[1][1] = -1; ras.C[2][1] = 0; ras.C[3][1] = 1;
        ras.C[0][2] = 1; ras.C[1][2] = 0; ras.C[2][2] = -1; ras.C[3][2] = 0;
        ras.C[0][3] = 0; ras.C[1][3] = 1; ras.C[2][3] = 0; ras.C[3][3] = -1;
        
        List<Integer> next = new ArrayList<Integer>(); next.add(0); next.add(1);
        ras.ConflictStages.add(next);
        
        ras.CalculateReachableStates();        
        ras.CalculateReachableSafeStates();
        ras.RemoveNonboundaryUnsafeStates();
        ras.CalculateMaxSafe();
        ras.CalculateSafeCount();*/
    	
        int linearcount = 0;
        for (int pn = 1; pn <= 1; pn++)
        {
            //Create a RAS from PN file
            RAS ras = new RAS(path + "pn" + pn + ".txt");


            List<RAS> MaximalPolicies = new ArrayList<RAS>();
            PriorityQueue<RAS> Explore = new PriorityQueue<RAS>();
            Explore.add(ras);
            int numExplored = 0;
            while (Explore.size() > 0)
            {
                numExplored++;
                RAS current = Explore.poll();
                if (!RASinPolicies(MaximalPolicies, current))
                {
                    if (current.LinearSpearable())
                    {
                        MaximalPolicies.add(current);
                        break;
                    }
                    else
                    {
                        List<Integer> CH = current.ConvexHull(); //new List<int>(current.MaxSafe);

                        for (int i = 0; i < CH.size(); i++)
                        {
                            RAS newras = new RAS(current, CH, i);
                            //newras.Prune(CH.get(i));
                            
                            Explore.add(newras);
                        }
                    }
                }
            }
            WriteMaximalRAS(pn, numExplored, MaximalPolicies);
            if (numExplored == 1)
                linearcount++;
            else
            {

            }
            //MessageBox.Show("There is " + MaximalPolicies.Count + " maximal linear policy");
        }
        System.out.println(linearcount + " out of 100 are linearly separable");
    }
    
    public void SolvePN()
    {
        /*RAS ras = new RAS();
        ras.p = 4;
        ras.r = 2;
        ras.t = 4;
        ras.m0 = new int[ras.p]; ras.m0[0] = 0; ras.m0[1] = 0; ras.m0[2] = 3; ras.m0[3] = 3;
        ras.C = new int[ras.p][ras.t];
        ras.C[0][0] = -1; ras.C[1][0] = 0; ras.C[2][0] = 1; ras.C[3][0] = 0;
        ras.C[0][1] = 0; ras.C[1][1] = -1; ras.C[2][1] = 0; ras.C[3][1] = 1;
        ras.C[0][2] = 1; ras.C[1][2] = 0; ras.C[2][2] = -1; ras.C[3][2] = 0;
        ras.C[0][3] = 0; ras.C[1][3] = 1; ras.C[2][3] = 0; ras.C[3][3] = -1;
        ras.StateDict.put("0,0", 0);
        List<Integer> next;
        ras.States.add("0,0,3,3"); next = new ArrayList<Integer>(); next.add(1);next.add(3);ras.NextStates.add(next);
        ras.States.add("0,1,3,2"); next = new ArrayList<Integer>(); next.add(0);next.add(2);next.add(8); ras.NextStates.add(next);
        ras.States.add("0,2,3,1"); next = new ArrayList<Integer>(); next.add(1);next.add(5);next.add(7); ras.NextStates.add(next);
        ras.States.add("1,0,2,3"); next = new ArrayList<Integer>(); next.add(0);next.add(4);next.add(8); ras.NextStates.add(next);
        ras.States.add("2,0,1,3"); next = new ArrayList<Integer>(); next.add(3);next.add(9);next.add(11); ras.NextStates.add(next);
        ras.States.add("0,3,3,0"); next = new ArrayList<Integer>(); next.add(6); ras.NextStates.add(next);
        ras.States.add("1,3,2,0"); next = new ArrayList<Integer>(); next.add(7); ras.NextStates.add(next);
        ras.States.add("1,2,2,1"); next = new ArrayList<Integer>(); next.add(8); ras.NextStates.add(next);
        ras.States.add("1,1,2,2"); next = new ArrayList<Integer>(); next.add(9); ras.NextStates.add(next);
        ras.States.add("2,1,1,2"); next = new ArrayList<Integer>(); next.add(10); ras.NextStates.add(next);
        ras.States.add("3,1,0,2"); next = new ArrayList<Integer>(); next.add(11); ras.NextStates.add(next);
        ras.States.add("3,0,0,3"); next = new ArrayList<Integer>(); next.add(10); ras.NextStates.add(next);
        ras.Safe = new ArrayList<Boolean>();
        for (int i = 0; i < 6; i++)
            ras.Safe.add(true);
        for (int i = 0; i < 5; i++)
            ras.Safe.add(false);
        ras.Safe.add(true);
        next = new ArrayList<Integer>(); next.add(0); next.add(1);
        ras.ConflictStages.add(next);
        ras.RemoveNonboundaryUnsafeStates();
        ras.CalculateMaxSafe();
        ras.CalculateSafeCount();*/
        
        int linearcount = 0;
        for (int pn = 1; pn <= 1; pn++)
        {
            //Create a RAS from PN file
            RAS ras = new RAS(path + "pn" + pn + ".txt");


            List<RAS> MaximalPolicies = new ArrayList<RAS>();
            Stack<RAS> Explore = new Stack<RAS>();
            Explore.push(ras);
            int numExplored = 0;
            while (Explore.size() > 0)
            {
                numExplored++;
                RAS current = Explore.pop();
                if (!RASinPolicies(MaximalPolicies, current))
                {
                    if (current.LinearSpearable())
                    {
                        MaximalPolicies = AddRASToPolicies(MaximalPolicies, current);
                    }
                    else
                    {
                        List<Integer> CH = current.ConvexHull(); //new List<int>(current.MaxSafe);

                        for (int i = 0; i < CH.size(); i++)
                        {
                        	RAS newras = new RAS(current, CH, i);

                            if (!RASinPolicies(MaximalPolicies, newras))
                            	Explore.push(newras);
                        }
                    }
                }
            }
            WriteMaximalRAS(pn, numExplored, MaximalPolicies);
            if (numExplored == 1)
                linearcount++;
        }
        System.out.println(linearcount + " out of 100 are linearly separable");
    }

  

    public void WriteResults()
    {
    	try
    	{
	    	BufferedWriter writer = new BufferedWriter(new OutputStreamWriter
	        		(new FileOutputStream(path + "Maximal IDs.txt")));
	      
	        for (int pn = 1; pn <= 1000; pn++)
	        {
	        	BufferedReader reader = new BufferedReader(new FileReader(path + "Maximal DAP" + pn + ".txt"));
	            String line = reader.readLine();
	            if (line .equals( "linear"))
	            {
	
	            }
	            else
	            {
	                writer.write(pn);
	                writer.newLine();
	            }
	            reader.close();
	        }
	        writer.close();
    	}
    	catch(Exception e)
    	{
    		
    	}
        System.out.println("Finished");
    }

}
