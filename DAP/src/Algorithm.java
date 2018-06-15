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
    	int p = ras1.p - ras1.r;
        for(int i : ras2.MaxSafe)
        {
        	boolean AnyGreater = false;
        	int[] ras2Max = ras2.States.get(i);
        	for(int j : ras1.MaxSafe)
        	{
        		boolean ThisGreater = true;
            	int[] ras1Max = ras1.States.get(j);
        		for(int k = 0; k < p; k++)
        		{
        			if(ras2Max[k] > ras1Max[k])
        			{
        				ThisGreater = false;
        				break;
        			}
        		}
        		if(ThisGreater)
        		{
        			AnyGreater = true;
        			break;
        		}
        	}
        	if(!AnyGreater)
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
    
    String join(String sep,int [] arr)
    {
    	String res = "";
    	for(int i=0;i<arr.length-1;i++)
    	{
    		res += arr[i]+sep;
    	}
    	res += arr[arr.length-1];
    	return res;
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
	            writer.write("" + numExplored);
	            writer.newLine();
	            writer.write("" + MaximalPolicies.size());
	            writer.newLine();
	            for (int i = 0; i < MaximalPolicies.size(); i++)
	            {
	                writer.write("" + i);
	                writer.newLine();
	                for (int itr = 0; itr < MaximalPolicies.get(i).States.size(); itr++)
	                {
	                    if (MaximalPolicies.get(i).Safe.get(itr))
	                    {
	                        writer.write(join(",", MaximalPolicies.get(i).States.get(itr)) );
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
            //RAS ras = new RAS(path + "pn" + pn + ".txt");
            RAS ras = new RAS(path + "PT222");


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
                        	RAS newras = new RAS(current);
                        	newras.Prune(CH.get(i), current);
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
            
        	//RAS ras = new RAS(path + "PT222");


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
                        	RAS newras = new RAS(current);
                        	newras.Prune(CH.get(i), current);

                            if (!RASinPolicies(MaximalPolicies, newras))
                            	Explore.push(newras);
                        }
                    }
                }
                if(numExplored % 5000 == 4999)
                	WriteMaximalRAS(pn, numExplored, MaximalPolicies);
                
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
