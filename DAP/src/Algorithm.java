import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.List;
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
        	//Ahmed not sure if index of workds
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
    public void SolvePN()
    {
        //////RAS ras = new RAS();
        //////ras.p = 2;
        //////ras.m0 = new int[2]; ras.m0[0] = 0; ras.m0[1] = 0;
        //////ras.StateDict = new Dictionary<String, int>(); ras.StateDict.Add("0,0", 0);
        //////ras.States = new List<String>();
        //////ras.NextStates = new List<List<int>>(); List<int> next;
        //////ras.States.Add("0,0"); next = new List<int>(); next.Add(1);next.Add(3);ras.NextStates.Add(next);
        //////ras.States.Add("0,1"); next = new List<int>(); next.Add(0);next.Add(2);next.Add(8); ras.NextStates.Add(next);
        //////ras.States.Add("0,2"); next = new List<int>(); next.Add(1);next.Add(5);next.Add(7); ras.NextStates.Add(next);
        //////ras.States.Add("1,0"); next = new List<int>(); next.Add(0);next.Add(4);next.Add(8); ras.NextStates.Add(next);
        //////ras.States.Add("2,0"); next = new List<int>(); next.Add(3);next.Add(9);next.Add(11); ras.NextStates.Add(next);
        //////ras.States.Add("0,3"); next = new List<int>(); next.Add(6); ras.NextStates.Add(next);
        //////ras.States.Add("1,3"); next = new List<int>(); next.Add(7); ras.NextStates.Add(next);
        //////ras.States.Add("1,2"); next = new List<int>(); next.Add(8); ras.NextStates.Add(next);
        //////ras.States.Add("1,1"); next = new List<int>(); next.Add(9); ras.NextStates.Add(next);
        //////ras.States.Add("2,1"); next = new List<int>(); next.Add(10); ras.NextStates.Add(next);
        //////ras.States.Add("3,1"); next = new List<int>(); next.Add(11); ras.NextStates.Add(next);
        //////ras.States.Add("3,0"); next = new List<int>(); next.Add(10); ras.NextStates.Add(next);
        //////ras.Safe = new List<bool>();
        //////for (int i = 0; i < 5; i++)
        //////    ras.Safe.Add(true);
        //////for (int i = 0; i < 7; i++)
        //////    ras.Safe.Add(false);
        int linearcount = 0;
        for (int pn = 1; pn <= 1; pn++)
        {
            boolean MAX = true; // This is set to true to find the largest linearly separable, otherwise it will find all linearly separable 
            int MAX_Size = 0;

            RAS ras = new RAS();
            ras.ReadPN(path + "pn" + pn + ".txt");
            boolean enumerable = ras.CalculateReachableStates();
            if (!enumerable)//state space is very large
            {
                WriteMaximalRAS(pn, 1, new ArrayList<RAS>());
                linearcount++;
                continue;
            }
            ras.CalculateReachableSafeStates();
            ras.RemoveUnnecessaryStates();
            // this function removes the resources markings from the states vectors
            ras.RemoveResourcesFromStates();
            ras.CalculateMaxSafe();
            ras.ConvexHull();
            ras.CalculateSafeCount();


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
                        if (MAX)
                        {
                            //Ahmed
                            //I think this is wrong-- we are not searching for the maximum sized
                            if (current.safeCount > MAX_Size)
                            {
                                MAX_Size = current.safeCount;
                                MaximalPolicies.clear();
                                MaximalPolicies.add(current);
                            }
                        }
                        else
                        {
                            MaximalPolicies = AddRASToPolicies(MaximalPolicies, current);
                        }
                    }
                    else
                    {
                        List<Integer> CH = current.ConvexHull(); //new List<int>(current.MaxSafe);

                        for (int i = 0; i < CH.size(); i++)
                        {
                            RAS newras = new RAS(current);
                            newras.Prune(CH.get(i));
                            if (MAX && (newras.safeCount <= MAX_Size))
                                continue;
                            //Ahmed
                            //Mising check condition-- uncomment
                            //if (!RASinPolicies(MaximalPolicies, newras))
                            Explore.push(newras);
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
