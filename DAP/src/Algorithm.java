
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
    int MaxExplore = 2000;
    int MinExplore = 100;
    int tempFile = 0;
    long startTime;
    List<Long> MaxPolicyTime = new ArrayList<Long>();
    List<Integer> MaxPolicySize = new ArrayList<Integer>();
    String RASInfo = "";
    
    public String WriteTempExplore(List<RAS> rass, int pn)
    {
    	String file = "" + pn + "temp" + tempFile + ".txt";
    	tempFile++;

    	try
    	{
	    	BufferedWriter writer = new BufferedWriter(new OutputStreamWriter
	        		(new FileOutputStream(path + file)));
	        
	    	writer.write("" + rass.size());
	    	writer.newLine();
            for(RAS ras: rass)
	        {
	            //writer.write(ras.toString());
	            //writer.newLine();
	            ras.WriteAsALine(writer);
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
        if(MaxPolicySize.size()==0)
        {
            MaxPolicySize.add(ras.safeCount);
            MaxPolicyTime.add(System.currentTimeMillis() - startTime);
        }
        else if (ras.safeCount > MaxPolicySize.get(MaxPolicySize.size() - 1))
        {
            MaxPolicySize.add(ras.safeCount);
            MaxPolicyTime.add(System.currentTimeMillis() - startTime);
        }
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
                    writer.write(RASInfo);
                    writer.newLine();
                    writer.write("" + MaxPolicySize.size());
                    writer.newLine();
                    for(int i = 0; i < MaxPolicySize.size(); i++)
                    {
                        writer.write("" + MaxPolicyTime.get(i) + "," + MaxPolicySize.get(i));
                        writer.newLine();
                    }
	        	writer.write("" + MaximalPolicies.get(0).safeCount);
	        	writer.newLine();
	        	for(int i = 0; i < RAS.NextStates.size(); i++)
	        	{
	        		if(MaximalPolicies.get(0).Safe.get(i))
	        		{
	        			writer.write(i + " :");
	        			for(int j : RAS.NextStates.get(i))
	        				if(MaximalPolicies.get(0).Safe.get(j))
	        					writer.write(" " + j);
	        			writer.newLine();
	        		}
	        	}
	        	
	        	for(int itr = 0; itr < MaximalPolicies.size(); itr++)
	        	{
	        		List<List<Double>> Plans = MaximalPolicies.get(itr).LinearPlans();
	        		writer.write("" + itr);
	                writer.newLine();
	        		int p = Plans.get(0).size() - 1;
	        		
	        		String[] Names = new String[p];
	        		Names[0] = "\\Pi_{1,1}"; Names[1] = "\\Pi_{1,2}"; Names[2] = "\\Pi_{1,3}"; Names[3] = "\\Pi_{1,4}";
	        		Names[4] = "\\Pi_{2,1}"; Names[5] = "\\Pi_{2,2}"; Names[6] = "\\Pi_{2,3}"; Names[7] = "\\Pi_{2,4}";; Names[8] = "\\Pi_{2,5}";
	        		Names[9] = "\\Pi_{3,1}"; Names[10] = "\\Pi_{3,2}"; Names[11] = "\\Pi_{3,3}"; Names[12] = "\\Pi_{3,4}";; Names[13] = "\\Pi_{3,5}";

	        		for(int i = 0; i < Plans.size(); i++)
	        		{
		                for(int j = 0; j < p ; j++)
		                {
		                	if(Plans.get(i).get(j) > 0)
		                		writer.write(" + " + Plans.get(i).get(j) + Names[j]);
		                }
	                	writer.write(" <= " + Plans.get(i).get(p));	
		                writer.newLine();
	        		}
	        	}
	        	
	            //writer.write("" + numExplored);
	            //writer.newLine();
	            //writer.write("" + MaximalPolicies.size());
	            //writer.newLine();
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
	                        writer.write(join(",", RAS.States.get(itr),RAS.p-RAS.r) );
	                        //writer.write(itr+" : "+join(",", RAS.States.get(itr),RAS.p-RAS.r) );
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
    

    public void SolvePN_fast()
    {
        
       Boolean first = true;
        startTime = System.currentTimeMillis();
        int linearcount = 0;
        //for (int pn = 558; pn <= 558; pn++)
        // 558, 565, 605, 621, 
        //642, 643, 897, 1010, 1026, 1034, 1040
        int pn = 445;
        {
           

            List<RAS> MaximalPolicies = new ArrayList<RAS>();
            RAS ras = new RAS(path + "PT" + pn);
            //RAS ras = new RAS(path + "PTSE");
            
            RASInfo = "Number of reachable safe states "+ras.safeCount;
            RASInfo += "\nNumber of maximal safe states "+ras.MaxSafe.size();
            RASInfo += "\nNumber of minimal unsafe states "+ras.MinBoundaryUnsafe.size();
            RASInfo += "\nDim = "+(ras.p-ras.r);
            
            /*MaximalPolicies.add(ras);
            WriteMaximalRAS(pn, 0, MaximalPolicies, new Stack<RAS>());
            for(int i = 0; i < ras.States.size(); i++)
            {
            	if((ras.States.get(i)[17] + ras.States.get(i)[18]) == 2)
            		ras.Safe.set(i, false);
            }
            ras.CalculateSafeCount();*/
            //Explore.add(ras);
            int numExplored = 0;
            
            int numRedundantMaxSafe = 0;
            int numDominated = 0;
            //RAS current = new RAS(ras);
            while (MaximalPolicies.size() == 0)
            {
                numExplored++;
                
                    if (ras.LinearSpearable())
                    {
                        MaximalPolicies = AddRASToPolicies(MaximalPolicies, ras);
                        //current.printMaxSafe();
                        System.out.println("A linear policy was found");
                    }
                    else
                    {
                        List<Integer> CH = ras.ConvexHull(); 
                        if(first)
                        {
                            first = false;
                            RASInfo += "\n Number of states to prune at the first step is " + CH.size();
                        }
                        ras = new RAS(ras, CH.get(CH.size() - 1));
                        ras.applyPruning();
                    }
                
                if(numExplored % 10 == 0)
                {
                	System.out.println("Number explored "+numExplored+ ", redundant = "+numRedundantMaxSafe+", dominated "+numDominated);
                	System.out.println("LP1 : " + RAS.lp1cnt + " LP2: " + RAS.lp2cnt);
                }
                
                //if((System.currentTimeMillis() - startTime > 48*3600*1000) && (MaximalPolicies.size() > 0))
                //if((System.currentTimeMillis() - startTime > 4*3600*1000))
                if((MaximalPolicies.size() > 0))
                {
                    System.out.println("Early exit");
                	System.out.println("LP1 : " + RAS.lp1cnt + " LP2: " + RAS.lp2cnt);
                    break;
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
  

    public void SolvePN_fast_new()
    {
        int major = 0; 
        int minor = 0;
        double MaxSafeCount = 0;
        int CurrentSafeCount = 0;
        Boolean first = true;
        startTime = System.currentTimeMillis();
        int linearcount = 0;
        //for (int pn = 558; pn <= 558; pn++)
        // 558, 565, 605, 621, 
        //642, 643, 897, 1010, 1026, 1034, 1040
        int pn = 642;
        {  

            List<RAS> MaximalPolicies = new ArrayList<RAS>();
            RAS ras = new RAS(path + "PT" + (pn));
            MaxSafeCount = ras.safeCount;
            RASInfo = "Number of reachable safe states "+ras.safeCount;
            RASInfo += "\nNumber of maximal safe states "+ras.MaxSafe.size();
            RASInfo += "\nNumber of minimal unsafe states "+ras.MinBoundaryUnsafe.size();
            RASInfo += "\nDim = "+(ras.p-ras.r);
            int numExplored = 0;
            
            int numRedundantMaxSafe = 0;
            int numDominated = 0;
            while (true)
            {
                numExplored++;
                major++;
                    if (ras.LinearSpearable())
                    {
                        MaximalPolicies = AddRASToPolicies(MaximalPolicies, ras);
                        CurrentSafeCount = ras.safeCount;
                        System.out.println("A linear policy was found");
                        break;
                    }
                    else
                    {
                        List<Integer> CH = ras.ConvexHull_new_3_1(); 
                        if(first)
                        {
                            first = false;
                            System.out.println("First LP created");
                            RASInfo += "\n Number of states to prune at the first step is " + CH.size();
                        }
                        
                    	Object[] temp = ras.MinBoundaryUnsafeUnseparable.toArray();
                    	int MinState = (int) temp[0];
                    	for(int i = 1; i < temp.length; i++)
                    		if(((int) temp[i]) < MinState)
                    			MinState = (int )temp[i];
                        
                    	boolean sep = false;
                        while(!sep)
                        {
                        	sep = true;
                        	if(temp.length == 0)
                        		break;
                            if(CH.size() == 0)
                            	break;
                        		//ras = new RAS(ras, CH.get(CH.size() - 1));
                                //ras.applyPruning();
                                List<Boolean> ParentSafe = new ArrayList<Boolean>(ras.Safe);
                        	    ras.reviewSafety(CH.get(CH.size() - 1));
                            	ras.UpdateMaxSafe(ParentSafe);
                            	ras.CalculateSafeCount();
                            	
                            	//ras.LinearSpearable();
                            sep = ras.LinearSpearable(MinState);
                            minor++;
                            CH.remove(CH.size() - 1);
                        }
                    }
                
                if(numExplored % 10 == 0)
                {
                	System.out.println("Number explored "+numExplored+ ", redundant = "+numRedundantMaxSafe+", dominated "+numDominated);
                	
                    System.out.println("Total time = "+(System.currentTimeMillis() - startTime)/1000);
                }
                
                //if((System.currentTimeMillis() - startTime > 48*3600*1000) && (MaximalPolicies.size() > 0))
                //if((System.currentTimeMillis() - startTime > 4*3600*1000))
                if((MaximalPolicies.size() > 0))
                {
                    System.out.println("Early exit");
                    System.out.println("Major "+major+ ", minor = "+minor);
                    break;
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
            
            System.out.println("Major "+major+ ", minor = "+minor);
        	
        }
        System.out.println(linearcount + " out of 100 are linearly separable");
        System.out.println("&"+((System.currentTimeMillis() - startTime)/1000.0)+"&"+CurrentSafeCount+"&"+(CurrentSafeCount/MaxSafeCount));
    }
    
   
    
    public void SolvePN()
    {
        
       Boolean first = true;
        startTime = System.currentTimeMillis();
        int linearcount = 0;
        //for (int pn = 558; pn <= 558; pn++)
        // 558, 565, 605, 621, 
        //642, 643, 897, 1010, 1026, 1034, 1040
        int pn = 474;
        {
           

            List<RAS> MaximalPolicies = new ArrayList<RAS>();
            Stack<RAS> Explore = new Stack<RAS>();
            //PriorityQueue<RAS> Explore = new PriorityQueue<RAS>();
            Stack<String> ExploreTempFiles = new Stack<String>();
            
            RAS ras = new RAS(path + "PT" + pn);
            
            RASInfo = "Number of reachable safe states "+ras.safeCount;
            RASInfo += "\nNumber of maximal safe states "+ras.MaxSafe.size();
            RASInfo += "\nNumber of minimal unsafe states "+ras.MinBoundaryUnsafe.size();
            RASInfo += "\nDim = "+(ras.p-ras.r);
            
            /*MaximalPolicies.add(ras);
            WriteMaximalRAS(pn, 0, MaximalPolicies, new Stack<RAS>());
            for(int i = 0; i < ras.States.size(); i++)
            {
            	if((ras.States.get(i)[17] + ras.States.get(i)[18]) == 2)
            		ras.Safe.set(i, false);
            }
            ras.CalculateSafeCount();*/
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
            		for(int itr = MaxExplore - MinExplore; itr < MaxExplore; itr++)
            			temp.add(Explore.pop());
            		ExploreTempFiles.add(WriteTempExplore(Explore, pn));
                        Explore.clear();
                        for(int itr = temp.size() - 1; itr >= 0; itr--)
                            Explore.add(temp.get(itr));
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
                        if(first)
                        {
                            first = false;
                            RASInfo += "\n Number of states to prune at the first step is " + CH.size();
                        }
                        for (int i = 0; i < CH.size(); i++)
                        {
                        	RAS newras = new RAS(current,CH.get(i));
                        	newras.applyPruning();
                        	 if (!RASinPolicies(MaximalPolicies, newras) && !exploredBefore(newras,exploredConfig))
                             	Explore.push(newras);
                             else
                             	numDominated++;
                        	 //List<RAS> MaximalPolicies2 = new ArrayList<RAS>();
                        	 //MaximalPolicies2.add(newras);
                        	 //WriteMaximalRAS(100, 0, MaximalPolicies2, new Stack<RAS>());
                        }
                        /*List<RAS> ToBePruned = new ArrayList<RAS>();
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
                        }*/
                    }
                    
                }
                else
                	numDominated++;
                if(numExplored % 10 == 0)
                {
                	System.out.println("Current stack size " + Explore.size() +  " ,number explored "+numExplored+ ", redundant = "+numRedundantMaxSafe+", dominated "+numDominated);
                }
                
                //if((System.currentTimeMillis() - startTime > 48*3600*1000) && (MaximalPolicies.size() > 0))
                //if((System.currentTimeMillis() - startTime > 48*3600*1000))
                if (MaximalPolicies.size() > 0)
                {
                    System.out.println("Early exit");
                    break;
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

   boolean exploredBefore(RAS current,List<List<HashSet<Integer>>> exploredConfig)
   {
	   for(HashSet<Integer> maxSafeSet:exploredConfig.get(current.safeCount))
	   {
		   if(current.MaxSafe.equals(maxSafeSet))
			   return true;
	   }
	   return false;
   }


}

