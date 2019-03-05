
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.PriorityQueue;
import java.util.Queue;
import java.util.Set;
import java.util.Stack;

import java.util.stream.IntStream; 
//import java.io.Writer;

class Algorithm
{
    String path;
    int MaxExplore = 100000;
    int MinExplore = 20000;
    int tempFile = 0;
    
    public String WriteTempExplore(List<RAS> rass)
    {
    	String file = "temp" + tempFile + ".txt";
    	tempFile++;

    	try
    	{
	    	BufferedWriter writer = new BufferedWriter(new OutputStreamWriter
	        		(new FileOutputStream(path + file)));
	        
	    	writer.write("" + rass.size());
	    	writer.newLine();
            for(RAS ras: rass)
	        {
	            writer.write(ras.toString());
	            writer.newLine();
	        }
	        writer.close();
    	}
    	catch(Exception e)
    	{
    		
    	}
    	
    	return file;
    }
    
    public List<RAS> ReadTempExplore(String file)
    {
    	List<RAS> rass = new ArrayList<RAS>();
    	try
    	{
	    	BufferedReader reader = new BufferedReader(new FileReader(path + file));
	    	
	    	int count = Integer.parseInt(reader.readLine());

	        for (int i = 0; i < count; i++)
	        {
	            RAS temp = new RAS(reader.readLine(), 0);
	            rass.add(temp);
	        }
	        
	        reader.close();
    	}
    	catch(Exception e)
    	{
    		
    	}
    	
    	return rass;
    }
    
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
    	int p = RAS.p - RAS.r;
        for(int i : ras2.MaxSafe)
        {
        	boolean AnyGreater = false;
        	int[] ras2Max = RAS.States.get(i);
        	for(int j : ras1.MaxSafe)
        	{
        		boolean ThisGreater = true;
            	int[] ras1Max = RAS.States.get(j);
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
    
    String join(String sep,int [] arr,int len)
    {
    	String res = "";
    	for(int i=0;i<len-1;i++)
    	{
    		res += arr[i]+sep;
    	}
    	res += arr[len-1];
    	return res;
    }

    public void WriteMaximalRAS(int pn, int numExplored, List<RAS> MaximalPolicies, Stack<RAS> Explore)
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
	                MaximalPolicies.get(i);
					for (int itr = 0; itr < RAS.States.size(); itr++)
	                {
	                    if (MaximalPolicies.get(i).Safe.get(itr))
		                //if (MaximalPolicies.get(i).MaxSafe.contains(itr))
	                    {
	                        writer.write(itr+" : "+join(",", RAS.States.get(itr),RAS.p-RAS.r) );
	                        writer.newLine();
	                    }
	                }
	            }
	        }
	        writer.close();
	        writer = new BufferedWriter(new OutputStreamWriter
	        		(new FileOutputStream(path + "Maximal DAP Stack " + pn + ".txt")));
            writer.write("" + Explore.size());
            writer.newLine();
            int index = 0;
            for(RAS policy: Explore)
            {
            	writer.write("" + index++);
            	writer.newLine();
                for (int itr = 0; itr < RAS.States.size(); itr++)
                {
                    if (policy.Safe.get(itr))
                    {
                        writer.write(join(",", RAS.States.get(itr),RAS.p-RAS.r) );
                        writer.newLine();
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
        RAS.p = 4;
        RAS.r = 2;
        RAS.t = 4;
        RAS.m0 = new int[RAS.p]; RAS.m0[0] = 0; RAS.m0[1] = 0; RAS.m0[2] = 3; RAS.m0[3] = 3;
        RAS.C = new int[RAS.p][RAS.t];
        RAS.C[0][0] = -1; RAS.C[1][0] = 0; RAS.C[2][0] = 1; RAS.C[3][0] = 0;
        RAS.C[0][1] = 0; RAS.C[1][1] = -1; RAS.C[2][1] = 0; RAS.C[3][1] = 1;
        RAS.C[0][2] = 1; RAS.C[1][2] = 0; RAS.C[2][2] = -1; RAS.C[3][2] = 0;
        RAS.C[0][3] = 0; RAS.C[1][3] = 1; RAS.C[2][3] = 0; RAS.C[3][3] = -1;
        
        List<Integer> next = new ArrayList<Integer>(); next.add(0); next.add(1);
        RAS.ConflictStages.add(next);
        
        ras.CalculateReachableStates();        
        ras.CalculateReachableSafeStates();
        ras.RemoveNonboundaryUnsafeStates();
        ras.CalculateMaxSafe();
        ras.CalculateSafeCount();*/
    	
        int linearcount = 0;
        for (int pn = 5; pn <= 5; pn++)
        {
            //Create a RAS from PN file
            //RAS ras = new RAS(path + "pn" + pn + ".txt");
            RAS ras = new RAS(path + "PT222");


            List<RAS> MaximalPolicies = new ArrayList<RAS>();
            //Queue<RAS> Explore = new LinkedList<>();
            PriorityQueue<RAS> Explore = new PriorityQueue<RAS>();
            Stack<String> ExploreTempFiles = new Stack<String>();
            
            Explore.add(ras);
            int numExplored = 0;
            while ((Explore.size() > 0) || (ExploreTempFiles.size() >0))
            {
            	if(Explore.size() == 0)
            	{
            		List<RAS> temp = ReadTempExplore(ExploreTempFiles.pop());
            		for(RAS tempras:temp)
            			Explore.add(tempras);
            	}
            	else if(Explore.size() > MaxExplore)
            	{
            		List<RAS> temp = new ArrayList<RAS>();
            		for(int itr = 0; itr < MaxExplore - MinExplore; itr++)
            			temp.add(Explore.poll());
            		ExploreTempFiles.add(WriteTempExplore(temp));
            	}
                numExplored++;
                RAS current = Explore.poll();
                current.applyPruning();
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
                    	RAS newras = new RAS(current,CH.get(i));
                    	newras.applyPruning();

                        Explore.add(newras);
                    }
                }

                if(numExplored % 5000 == 4999)
                {
                	System.out.println("The algorithm has explored " + numExplored + " subspaces, and there is " + Explore.size() + " subspaces in stack");
                }
            }
            WriteMaximalRAS(pn, numExplored, MaximalPolicies, new Stack<RAS>());
            if (numExplored == 1)
                linearcount++;
            else
            {

            }
            //MessageBox.Show("There is " + MaximalPolicies.Count + " maximal linear policy");
        }
        System.out.println(linearcount + " out of 100 are linearly separable");
    }
    
    public void SolvePNMax2()
    {
       
        int linearcount = 0;
        int maxsize = 0;
        long startTime = System.currentTimeMillis();
        for (int pn = 5; pn <= 5; pn++)
        {
            List<RAS> MaximalPolicies = new ArrayList<RAS>();
            Stack<RAS> Explore = new Stack<RAS>();
            Stack<String> ExploreTempFiles = new Stack<String>();
            
            RAS ras = new RAS(path + "PT222");
            Explore.push(ras);
            int numExplored = 0;
            List<List<HashSet<Integer>>> exploredConfig = new ArrayList<List<HashSet<Integer>>>();
            for(int itr = 0; itr <= ras.safeCount; itr++)
            	exploredConfig.add(new ArrayList<HashSet<Integer>>());
            int numRedundantMaxSafe = 0;
            int numDominated = 0;
            while ((Explore.size() > 0) || (ExploreTempFiles.size() > 0))
            {
            	//read one file from temp files
            	if(Explore.size() == 0)
            	{
            		List<RAS> temp = ReadTempExplore(ExploreTempFiles.pop());
            		for(RAS tempras:temp)
            			Explore.push(tempras);
            	}
            	else if(Explore.size() > MaxExplore)
            	{
            		List<RAS> temp = new ArrayList<RAS>();
            		for(int itr = 0; itr < MaxExplore - MinExplore; itr++)
            			temp.add(Explore.pop());
            		ExploreTempFiles.add(WriteTempExplore(temp));
            	}
                numExplored++;
                RAS current = Explore.pop();
                if(current.safeCount <= maxsize)
                	continue;
                
                //current.applyPruning();
                if(exploredBefore(current,exploredConfig))
                {
                	numRedundantMaxSafe++;
                	continue;
                }
                exploredConfig.get(current.safeCount).add(current.MaxSafe);
                if (!RASinPolicies(MaximalPolicies, current))
                {	
                    if (current.LinearSpearable())
                    {
                        maxsize = current.safeCount;
                    	MaximalPolicies.clear();
                        MaximalPolicies = AddRASToPolicies(MaximalPolicies, current);
                        System.out.println("A linear policy was found, current size is " + maxsize);
                    }
                    else
                    {
                        List<Integer> CH = current.ConvexHull(); //new List<int>(current.MaxSafe);
                        /*for (int i = 0; i < CH.size(); i++)
                        {
                        	RAS newras = new RAS(current,CH.get(i));
                        	newras.applyPruning();
                        	if(newras.safeCount <= maxsize)
                            	continue;
                        	
                        	 if (!RASinPolicies(MaximalPolicies, newras) && !exploredBefore(newras,exploredConfig))
                             	Explore.push(newras);
                             else
                             	numDominated++;
                        }
                        */
                        List<RAS> ToBePruned = new ArrayList<RAS>();
                        for(int i = 0; i < CH.size(); i++)
                        {
                        	ToBePruned.add(new RAS(current,CH.get(i)));
                        }
                        IntStream.range(0, CH.size()).parallel().forEach(i -> {ToBePruned.get(i).applyPruning();});
                        for(int i = 0; i < CH.size(); i++)
                        {
                        	 if(ToBePruned.get(i).safeCount <= maxsize)
                            	continue;
	                       	 if (!RASinPolicies(MaximalPolicies, ToBePruned.get(i)) && !exploredBefore(ToBePruned.get(i),exploredConfig))
	                          	Explore.push(ToBePruned.get(i));
	                          else
	                          	numDominated++;
                        }
                    }
                    
                }
                else
                	numDominated++;
                if(numExplored % 10 == 0)
                {
                	System.out.println("Current stack size " + Explore.size() +  " ,number explored "+numExplored+ ", redundant = "+numRedundantMaxSafe+", dominated "+numDominated);
                }
                
            }
            long duration = System.currentTimeMillis() - startTime;
            System.out.println("Total time = "+duration/1000);
            System.out.println("Total Explored = "+numExplored);
            System.out.println("Redundant Config = "+numRedundantMaxSafe);
            System.out.println("Dominated by maximal policies = "+numDominated);
            WriteMaximalRAS(pn, numExplored, MaximalPolicies, Explore);
            if (numExplored == 1)
                linearcount++;
        }
        System.out.println(linearcount + " out of 100 are linearly separable");
    }
    
    public void SolvePN()
    {
       
        int linearcount = 0;
        long startTime = System.currentTimeMillis();
        for (int pn = 1; pn <= 1; pn++)
        {
           

            List<RAS> MaximalPolicies = new ArrayList<RAS>();
            Stack<RAS> Explore = new Stack<RAS>();
            //PriorityQueue<RAS> Explore = new PriorityQueue<RAS>();
            Stack<String> ExploreTempFiles = new Stack<String>();
            
            RAS ras = new RAS(path + "PTS1");
            Explore.push(ras);
            //Explore.add(ras);
            int numExplored = 0;
            List<List<HashSet<Integer>>> exploredConfig = new ArrayList<List<HashSet<Integer>>>();
            for(int itr = 0; itr <= ras.safeCount; itr++)
            	exploredConfig.add(new ArrayList<HashSet<Integer>>());
            
            int numRedundantMaxSafe = 0;
            int numDominated = 0;
            while ((Explore.size() > 0) || (ExploreTempFiles.size() > 0))
            {
            	//read one file from temp files
            	if(Explore.size() == 0)
            	{
            		List<RAS> temp = ReadTempExplore(ExploreTempFiles.pop());
            		for(RAS tempras:temp)
            			Explore.push(tempras);
            	}
            	else if(Explore.size() > MaxExplore)
            	{
            		List<RAS> temp = new ArrayList<RAS>();
            		for(int itr = 0; itr < MaxExplore - MinExplore; itr++)
            			temp.add(Explore.pop());
            		ExploreTempFiles.add(WriteTempExplore(temp));
            	}
                numExplored++;
                RAS current = Explore.pop();
                //RAS current = Explore.poll();
                //current.applyPruning();
                if(exploredBefore(current,exploredConfig))
                {
                	numRedundantMaxSafe++;
                	continue;
                }
                exploredConfig.get(current.safeCount).add(current.MaxSafe);
                if (!RASinPolicies(MaximalPolicies, current))
                {	
                    if (current.LinearSpearable())
                    {
                        MaximalPolicies = AddRASToPolicies(MaximalPolicies, current);
                        //current.printMaxSafe();
                        System.out.println("A linear policy was found");
                    }
                    else
                    {
                        List<Integer> CH = current.ConvexHull(); //new List<int>(current.MaxSafe);
                        /*for (int i = 0; i < CH.size(); i++)
                        {
                        	RAS newras = new RAS(current,CH.get(i));
                        	newras.applyPruning();
                        	 if (!RASinPolicies(MaximalPolicies, newras) && !exploredBefore(newras,exploredConfig))
                             	Explore.push(newras);
                             else
                             	numDominated++;
                        }*/
                        List<RAS> ToBePruned = new ArrayList<RAS>();
                        for(int i = 0; i < CH.size(); i++)
                        {
                        	ToBePruned.add(new RAS(current,CH.get(i)));
                        }
                        IntStream.range(0, CH.size()).parallel().forEach(i -> {ToBePruned.get(i).applyPruning();});
                        for(int i = 0; i < CH.size(); i++)
                        {
	                       	 if (!RASinPolicies(MaximalPolicies, ToBePruned.get(i)) && !exploredBefore(ToBePruned.get(i),exploredConfig))
	                          	Explore.push(ToBePruned.get(i));
	                          else
	                          	numDominated++;
                        }
                    }
                    
                }
                else
                	numDominated++;
                if(numExplored % 10 == 0)
                {
                	System.out.println("Current stack size " + Explore.size() +  " ,number explored "+numExplored+ ", redundant = "+numRedundantMaxSafe+", dominated "+numDominated);
                }
                
            }
            long duration = System.currentTimeMillis() - startTime;
            System.out.println("Total time = "+duration/1000);
            System.out.println("Total Explored = "+numExplored);
            System.out.println("Redundant Config = "+numRedundantMaxSafe);
            System.out.println("Dominated by maximal policies = "+numDominated);
            System.out.println("Number of maximal policies = "+MaximalPolicies.size());
            WriteMaximalRAS(pn, numExplored, MaximalPolicies, new Stack<RAS>());
            if (numExplored == 1)
                linearcount++;
        }
        System.out.println(linearcount + " out of 100 are linearly separable");
    }
    
    
    public void SolvePN1()
    {
        
        
        int linearcount = 0;
        long startTime = System.currentTimeMillis();
        for (int pn = 1; pn <= 1; pn++)
        {
            
            List<RAS> MaximalPolicies = new ArrayList<RAS>();
            PriorityQueue<RAS> Explore = new PriorityQueue<RAS>();

        	
            
            RAS ras = new RAS(path + "pn9.txt");
            Explore.add(ras);
            int numExplored = 0;
            List<List<HashSet<Integer>>> exploredConfig = new ArrayList<List<HashSet<Integer>>>();
            for(int itr = 0; itr <= ras.safeCount; itr++)
            	exploredConfig.add(new ArrayList<HashSet<Integer>>());
            int numRedundantMaxSafe = 0;
            int numDominated = 0;
            while (Explore.size() > 0)
            {
                numExplored++;
                RAS current = Explore.poll();
                current.applyPruning();
                if(exploredBefore(current,exploredConfig))
                {
                	numRedundantMaxSafe++;
                	continue;
                }
                exploredConfig.get(current.safeCount).add(current.MaxSafe);
                if (!RASinPolicies(MaximalPolicies, current))
                {	
                    if (current.LinearSpearable())
                    {
                        MaximalPolicies = AddRASToPolicies(MaximalPolicies, current);
                        //current.printMaxSafe();
                        //System.out.println("A linear policy was found");
                    }
                    else
                    {
                        List<Integer> CH = current.ConvexHull(); //new List<int>(current.MaxSafe);

                        for (int i = 0; i < CH.size(); i++)
                        {
                        	RAS newras = new RAS(current,CH.get(i));
                        	

                            if (!RASinPolicies(MaximalPolicies, newras))
                            	Explore.add(newras);
                            else
                            	numDominated++;;
                        }
                    }
                    
                }
                else
                	numDominated++;
                
            }
            long duration = System.currentTimeMillis() - startTime;
            System.out.println("Total time = "+duration/1000);
            System.out.println("Total Explored = "+numExplored);
            System.out.println("Redundant Config = "+numRedundantMaxSafe);
            System.out.println("Dominated by maximal policies = "+numDominated);
            System.out.println("Number of maximal policies = "+MaximalPolicies.size());
            if (numExplored == 1)
                linearcount++;
        }
        System.out.println(linearcount + " out of 100 are linearly separable");
    }


   boolean exploredBefore(RAS current,List<List<HashSet<Integer>>> exploredConfig)
   {
	   for(HashSet<Integer> maxSafeSet:exploredConfig.get(current.safeCount))
	   {
		   if(current.MaxSafe.equals(maxSafeSet))
			   return true;
	   }
	   return false;
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
	            //if (line .equals( "linear"))
	            //{
	
	            //}
	            //else
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