import java.io.BufferedReader;
//import java.io.BufferedWriter;
//import java.io.FileInputStream;
//import java.io.FileOutputStream;
import java.io.FileReader;
//import java.io.InputStream;
//import java.io.InputStreamReader;
//import java.io.OutputStreamWriter;
//import java.io.Reader;
//import java.io.Writer;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
//import java.util.Set;
import java.util.Stack;

import ilog.concert.*;
//import ilog.concert.IloCopyManager.Check;
import ilog.cplex.*;

public class RAS implements Comparable<RAS>
{
    public static int p;
    public static int t;
    public static int r;
    public static int[] m0;
    public static int[][] C;
    public int safeCount;

    public static List<int []> States = new ArrayList<int []>();
    public List<Boolean> Safe = new ArrayList<Boolean>();
    public HashSet<Integer> MaxSafe = new HashSet<Integer>();
    public HashSet<Integer> MinBoundaryUnsafe = new HashSet<Integer>();
    //public HashSet<Integer> BoundaryUnsafe = new HashSet<Integer>();
    public HashSet <Integer> myConvexHullStates = new HashSet <Integer>();
    public HashSet <Integer> parentConvexHullStates = null;
    public static List<HashSet<Integer>> NextStates = new ArrayList<HashSet<Integer>>();
    public static List<HashSet<Integer>> PreviousStates = new ArrayList<HashSet<Integer>>();
    public static Map<String, Integer> StateDict = new HashMap<String, Integer>();
    public static List<List<Integer>> ConflictStages = new ArrayList<List<Integer>>();

    public void CalculateSafeCount()
    {
        safeCount = 0;
        for (int i = 0; i < Safe.size(); i++)
            if (Safe.get(i))
                safeCount++;
    }

    public List<Integer> ConvexHull()
    {
    	p = p - r;
    	List<Integer> points = new ArrayList<Integer>();
        List<Integer> SafeIDX = new ArrayList<Integer>();
        int NumberOfVertices = MaxSafe.size()/* + 1*/;
        //Why do we need zero
        //SafeIDX.add(0);
        for (int i : MaxSafe)
        {
        	SafeIDX.add(i);
        }

        double[][] vertices = new double[p] [NumberOfVertices];
        for (int i = 0; i < SafeIDX.size(); i++)
        {
        	int[] x = States.get(SafeIDX.get(i));
            for (int j = 0; j < p; j++)
                vertices[j][i] = x[j];
        }
        for (int MSstate : MaxSafe)
        {
            // If the maximal state is on the convex hull of the states before pruning
            // then, it is on the convex hull of the states after pruning.
            if(parentConvexHullStates != null && parentConvexHullStates.contains(MSstate))
            {
            	points.add(MSstate);
            	continue;
            }

 
            try
            {
            	//The index of the state that we are considering from the set of safe states
            	int itr1 = SafeIDX.indexOf(MSstate);
            	
            	IloCplex cplex = new IloCplex();
            	cplex.setOut(null);
            	cplex.setParam(IloCplex.DoubleParam.TiLim, 60);
            	IloObjective modelObj = cplex.addMaximize();
            	IloRange [] rng = new IloRange[p+1];
            	for (int j = 0; j < p; j++)
            		rng[j] = cplex.addRange(vertices[j][itr1],vertices[j][itr1], "coverDim"+j);
            	rng[p] = cplex.addRange(1,1, "convex");
            	IloNumVarArray var = new IloNumVarArray();
            	for(int i=0;i<NumberOfVertices;i++)
            	{
            		IloColumn column;
            		if(i== itr1)
            			column = cplex.column(modelObj, 0);
            		else
            			column = cplex.column(modelObj, 1);
            		
     	            for ( int j = 0; j < p; j++ )
     	               column = column.and(cplex.column(rng[j], vertices[j][i]));
     	            column = column.and(cplex.column(rng[p], 1));
     	            var.add(cplex.numVar(column, 0., 1 ,"h"+i));
            	}
            	//cplex.exportModel("convex"+Integer.toString(itr1)+".lp");
                if (cplex.solve())
                {
                	double objective = cplex.getObjValue();
                	double eps = 10e-6;
                	if(objective < eps)
                		points.add(SafeIDX.get(itr1));
       			}
                cplex.end();
               
            }
            catch (Exception e)
            {
                System.out.println("Concert exception caught: " + e);
            }

        }

        myConvexHullStates.addAll(points);
        p = p + r;
        return points;
    }

    public void ReadPN(String file)
    {
        try
    	{
	    	BufferedReader reader = new BufferedReader(new FileReader(file));
	        p = Integer.parseInt(reader.readLine());
	        t = Integer.parseInt(reader.readLine());
	        r = Integer.parseInt(reader.readLine());
	        m0 = new int[p];
	        C = new int[p][ t];
	        String[] tokens2 = reader.readLine().split("\t");
	        for (int i = 0; i < p; i++)
	            m0[i] = Integer.parseInt(tokens2[i]);
	        for (int i = 0; i < p; i++)
	        {
	            String[] tokens = reader.readLine().split("\t");
	            for (int j = 0; j < t; j++)
	                C[i][ j] = Integer.parseInt(tokens[j]);
	        }
	        // This is for the conflict processing stages
	        if (reader.readLine() .equals( "Conflict"))
	        {
	            String line = "";
	            while ((line = reader.readLine()) != null)
	            {
	                String[] tokens = line.split(",");
	                List<Integer> temp = new ArrayList<Integer>();
	                for (int j = 0; j < tokens.length; j++)
	                    temp.add(Integer.parseInt(tokens[j]));
	                ConflictStages.add(temp);
	            }
	        }
	        reader.close();
    	}
    	catch(Exception e)
    	{
    		
    	}
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
    /// <summary>
    /// uses the C matrix and the initial marking to calculate all the reachable states
    /// </summary>
    public void CalculateReachableStates()
    {
        int currentState = 0;
        StateDict.put(join(",", m0), 0);
        States.add(m0);

        while (currentState < States.size())
        {
            //0- Initialize the next states
        	HashSet<Integer> next = new HashSet<Integer>();
            //1- Get the state that you want to explore
            int[] s = new int[p];
            for (int i = 0; i < p; i++)
                s[i] = States.get(currentState)[i];
            //2- Make sure that the state doesn't have any stage conflict
            boolean conflict = false;
            for (int j = 0; j < ConflictStages.size(); j++)
            {
                int NonZeroCount = 0;
                for (int k = 0; k < ConflictStages.get(j).size(); k++)
                {
                    if (States.get(currentState)[ConflictStages.get(j).get(k)] != 0)
                        NonZeroCount++;
                }
                if (NonZeroCount >= 2)
                    conflict = true;
            }
            //3- If there is no conflict explore reachable states from the current state 
            if (!conflict)
            {
                for (int j = 0; j < t; j++)
                {
                    boolean reachable = true;
                    int[] m = new int[p];
                    for (int i = 0; i < p; i++)
                    {
                        m[i] = s[i];
                        m[i] += C[i][j];
                        if (m[i] < 0)
                            reachable = false;
                    }
                    if (reachable)
                    {
                        if (!StateDict.containsKey(join(",", m)))
                        {
                            StateDict.put(join(",", m), States.size());
                            States.add(m);
                        }
                        next.add(StateDict.get(join(",", m)));
                    }
                }
            }
            //4-
            NextStates.add(next);

            //5-
            currentState++;

        }

    }

    /// <summary>
    /// divide the reachable states to safe and unsafe
    /// </summary>
    public void CalculateReachableSafeStates()
    {
        for (int i = 0; i < States.size(); i++)
            Safe.add(false);
        Safe.set(0, true);
        boolean change = true;
        while (change)
        {
            change = false;
            for (int i = 0; i < States.size(); i++)
            {
                if (!Safe.get(i)) // not known yet
                {
                    for (int j : NextStates.get(i))
                        if (Safe.get(j))
                        {
                            change = true;
                            Safe.set(i, true);
                        }
                }
            }

        }

        for(int i = 0; i < States.size(); i++)
        {
        	HashSet<Integer> temp = new HashSet<Integer>();
        	PreviousStates.add(temp);
        }
        for(int i = 0; i < NextStates.size(); i++)
        {
        	for(int j : NextStates.get(i))
        	{
        		PreviousStates.get(j).add(i);
        	}
        }
    }

    public void RemoveNonboundaryUnsafeStates()
    {
        CalculateMaxSafe();
        for (int i = States.size() - 1; i >= 0; i--)
        {
            if (!Safe.get(i) && !MinBoundaryUnsafe.contains(i))
            {
                NextStates.set(i, new HashSet<Integer>());
                PreviousStates.set(i, new HashSet<Integer>());
                for (int itr = 0; itr < States.size(); itr++)
                {
                	if(NextStates.get(itr).contains(i))
                		NextStates.get(itr).remove(new Integer(i));
                	if(PreviousStates.get(itr).contains(i))
                		PreviousStates.get(itr).remove(new Integer(i));
                }
                //StateDict.Remove(States[i]);
                States.set(i, null);
            }
        }

        int newidx = States.indexOf(null);
        if (newidx == -1)
            return;
        for (int i = States.indexOf(null); i < States.size(); i++)
        {
        	//Ahmed might be problematic
            if (States.get(i) != null)
            {
                States.set(newidx, States.get(i));
                States.set(i, null);
                Safe.set(newidx, Safe.get(i));
                NextStates.set(newidx, new HashSet<Integer>(NextStates.get(i)));
                PreviousStates.set(newidx, new HashSet<Integer>(PreviousStates.get(i)));
                //StateDict[States[newidx]] = newidx;

                for (int itr = 0; itr < NextStates.size(); itr++)
                {
                    if (NextStates.get(itr).contains(i))
                    {
                    	NextStates.get(itr).remove(i);
                    	NextStates.get(itr).add(newidx);
                    }
                    
                    if (PreviousStates.get(itr).contains(i))
                    {
                    	PreviousStates.get(itr).remove(i);
                    	PreviousStates.get(itr).add(newidx);
                    }
                }
                newidx++;
                continue;
            }

        }
        for (int i = States.size() - 1; i > 0; i--)
        {
            if (States.get(i) == null)
            {
            	//Ahmed remove also might be problematic
                States.remove(i);
                NextStates.remove(i);
                PreviousStates.remove(i);
                Safe.remove(i);
            }
        }
        StateDict.clear();
        for(int i = 0; i < States.size(); i++)
        	StateDict.put(join(",", States.get(i)), i);


    }

    
    /// <summary>
    /// calculate the maximal safe and the minimal unsafe states
    /// </summary>
    public void CalculateMaxSafe()
    {
        MinBoundaryUnsafe = new HashSet<Integer>();
        for (int i = 0; i < States.size(); i++)
        {
            if (!Safe.get(i))
            {
                for (int j : PreviousStates.get(i))
                {
                    if (Safe.get(j))
                    {
                    	MinBoundaryUnsafe.add(i);
                    	break;
                    }
                }
            }
        }
        //
        Object[] array = MinBoundaryUnsafe.toArray();
        for (int itr = array.length - 1; itr >= 0; itr--)
        {
            boolean remove = false;
            int[] tokens1 = States.get((int)array[itr]);

            for (int j = 0; j < array.length; j++)
            {
                if (j == itr)
                    continue;
                boolean AllGreaterOrEqual = true;
                int[] tokens2 = States.get((int)array[j]);
                for (int k = 0; k < p - r; k++)
                {
                    if (tokens1[k] < tokens2[k])
                    {
                        AllGreaterOrEqual = false;
                        break;
                    }
                }
                if (AllGreaterOrEqual)
                {
                    remove = true;
                    break;
                }
            }
            if (remove)
            {
            	MinBoundaryUnsafe.remove((int)array[itr]);
            }
        }
        
        //
        MaxSafe = new HashSet<Integer>();
        for(int i = 0; i < States.size(); i++)
        {
            if(Safe.get(i))
            {
                MaxSafe.add(i);
            }
        }
        
        Object[] arr = MaxSafe.toArray();
        for(int itr = arr.length - 1; itr >= 0; itr--)
        {
        	boolean remove = false;
            int[] tokens1 = States.get((int)arr[itr]);

            for (int j = 0; j < arr.length; j++)
            {
                if (j == itr)
                    continue;
                boolean AllLessOrEqual = true;
                int[] tokens2 = States.get((int)arr[j]); 
                for (int k = 0; k < p - r; k++)
                {
                    if(tokens1[k] > tokens2[k])
                    {
                        AllLessOrEqual = false;
                        break;
                    }
                }
                if(AllLessOrEqual)
                {
                    remove = true;
                    break;
                }
            }
            if(remove)
            {
                MaxSafe.remove((int)arr[itr]);
            }
        }

    }
    

    public void CalculateMaxSafe(RAS parent)
    {
        MinBoundaryUnsafe = new HashSet<Integer>(parent.MinBoundaryUnsafe);
        HashSet<Integer> Changed = new HashSet<Integer>();
        for(int i = 0; i < States.size(); i++)
        	if(parent.Safe.get(i) && !Safe.get(i))
        		Changed.add(i);

        for(int i : Changed)
        {
        	for(int j : PreviousStates.get(i))
        	{
        		if(Safe.get(j))
        		{
        			MinBoundaryUnsafe.add(i);
        			break;
        		}
        	}
        }
        //
        Object[] array = MinBoundaryUnsafe.toArray();
        for (int itr = array.length - 1; itr >= 0; itr--)
        {
            boolean remove = false;
            int[] tokens1 = States.get((int)array[itr]);

            for (int j = 0; j < array.length; j++)
            {
                if (j == itr)
                    continue;
                boolean AllGreaterOrEqual = true;
                int[] tokens2 = States.get((int)array[j]);
                for (int k = 0; k < p - r; k++)
                {
                    if (tokens1[k] < tokens2[k])
                    {
                        AllGreaterOrEqual = false;
                        break;
                    }
                }
                if (AllGreaterOrEqual)
                {
                    remove = true;
                    break;
                }
            }
            if (remove)
            {
            	MinBoundaryUnsafe.remove((int)array[itr]);
            }
        }
        
        //
        Changed.clear();
        MaxSafe = new HashSet<Integer>();
        for(int ParentMaxSafe : parent.MaxSafe)
        	if(Safe.get(ParentMaxSafe))
        		MaxSafe.add(ParentMaxSafe);
        
        for(int i = 0; i < States.size(); i++)
        {
        	if(MaxSafe.contains(i))
        		continue;
            if(Safe.get(i))
            {
            	boolean remove = false;
            	int[] tokens1 = States.get(i);

                for (int j : MaxSafe)
                {
                    boolean AllLessOrEqual = true;
                    int[] tokens2 = States.get(j); 
                    for (int k = 0; k < p - r; k++)
                    {
                        if(tokens1[k] > tokens2[k])
                        {
                            AllLessOrEqual = false;
                            break;
                        }
                    }
                    if(AllLessOrEqual)
                    {
                        remove = true;
                        break;
                    }
                }
                if(!remove)
                {
                    MaxSafe.add(i);
                }
            }
        }
        
        Object[] arr = MaxSafe.toArray();
        for(int itr = arr.length - 1; itr >= 0; itr--)
        {
        	boolean remove = false;
            int[] tokens1 = States.get((int)arr[itr]);

            for (int j = 0; j < arr.length; j++)
            {
                if (j == itr)
                    continue;
                boolean AllLessOrEqual = true;
                int[] tokens2 = States.get((int)arr[j]); 
                for (int k = 0; k < p - r; k++)
                {
                    if(tokens1[k] > tokens2[k])
                    {
                        AllLessOrEqual = false;
                        break;
                    }
                }
                if(AllLessOrEqual)
                {
                    remove = true;
                    break;
                }
            }
            if(remove)
            {
                MaxSafe.remove((int)arr[itr]);
            }
        }

    }

    /// <summary>
    /// mark one of the states to be unsafe and modify the data accordingly
    /// </summary>
    /// <param name="state"></param>
    public void Prune(int PrunedState, RAS Parent)
    {
    	// lines 1-4 of the algorithm
    	//The set S will contains all the states s such that
    	//s <= s'' for s'' \in \bar{S} (the maximal of the parent) except the pruned state
    	Safe.set(PrunedState, false);
    	HashSet<Integer> Shat_r = new HashSet<Integer>();
    	for(int i = 0; i < Safe.size() ;i++)
    		if(Safe.get(i))
    			Shat_r.add(i);

    	
    	
    	Stack<Integer> Explore = new Stack<Integer>();
    	HashSet<Integer> Tested = new HashSet<Integer>();
    	
    	// line 5-7 of the algorithm
    	HashSet<Integer> Shat_rs = new HashSet<Integer>();
    	Tested.clear();
    	Explore.add(0);
    	while(Explore.size() > 0)
    	{
    		int current = Explore.pop();
    		for(int topush : RAS.PreviousStates.get(current))
    		{
    			if(Shat_r.contains(topush))
    			{
    				if(!Tested.contains(topush))
    				{
    					Shat_rs.add(topush);
    					Explore.add(topush);
    					Tested.add(topush);
    				}
    			}
    			
    		}
    	}

    	for(int i = 0; i < Safe.size(); i++)
    		Safe.set(i,  false);
    	for(int i : Shat_rs)
    		Safe.set(i, true);
    	// line 8 of the algorithm
        CalculateMaxSafe(Parent); 
       /* System.out.println("Number of reachable safe states before pruning "+Shat_r.size());
        System.out.println("Number of reachable safe states after pruning "+Shat_rs.size());
        System.out.println("Number of maximal safe states "+MaxSafe.size());
        System.out.println("Number of minimal unsafe states "+MinBoundaryUnsafe.size());
        printStates2();*/
        // This calculates the number of safe states
        CalculateSafeCount();
    }

    /// <summary>
    /// check whether the maximal safe and minimal unsafe are linearly separable or not.
    /// </summary>
    /// <returns></returns>
    public boolean LinearSpearable()
    {
    	p = p - r;
        //Ahmed -- M can be set to p * max val in states
        double M = 1000;
        double eps = 0.0001;
        // Solve the MIP from the file
        try
        {
            IloCplex cplex = new IloCplex();
            cplex.setOut(null);
        	cplex.setParam(IloCplex.DoubleParam.TiLim, 60);
            IloObjective modelObj = cplex.addMaximize();
        	IloRange [][] rng = new IloRange[2][];
        	rng[0] = new IloRange[MaxSafe.size()];
        	rng[1] = new IloRange[MinBoundaryUnsafe.size()];
        	for (int i = 0; i < MaxSafe.size(); i++)
        		rng[0][i] = cplex.addRange(Double.MAX_VALUE*-1,0, "Safe"+i);
        	for (int i = 0; i < MinBoundaryUnsafe.size(); i++)
        		rng[1][i] = cplex.addRange(eps-M,Double.MAX_VALUE, "Unsafe"+i);
        	IloNumVarArray var = new IloNumVarArray();
        	//Hyerplane coefficients
        	for(int j=0;j<p;j++)
        	{
        		 IloColumn column = cplex.column(modelObj, 0);
        		 int itr = 0;
        		 for (int MSsafe : MaxSafe)
        		 {
        			 int[] x = States.get(MSsafe);
        			 if(x[j] != 0)
        				 column = column.and(cplex.column(rng[0][itr], x[j]));
        			 itr++;
        		 }
        		 itr = 0;
        		 for (int MinUnsafe : MinBoundaryUnsafe)
        		 {
        			 int[] x = States.get(MinUnsafe);
        			 if(x[j] != 0)
        				 column = column.and(cplex.column(rng[1][itr], x[j]));
        			 itr++;
        		 }
 	             var.add(cplex.numVar(column, 0., 1 ,"a"+j));
        	}
        	//Intercept
        	IloColumn columnB = cplex.column(modelObj, 0);
        	for (int i = 0; i < MaxSafe.size(); i++)
        		columnB = columnB.and(cplex.column(rng[0][i], -1));
        	for (int i = 0; i < MinBoundaryUnsafe.size(); i++)
        		columnB = columnB.and(cplex.column(rng[1][i], -1));
        	 var.add(cplex.numVar(columnB, 0., 1 ,"b"));
        	//Indicators for separation
        	for (int i = 0; i < MinBoundaryUnsafe.size(); i++)
        	{
        		IloColumn column = cplex.column(modelObj, 1);
        		column = column.and(cplex.column(rng[1][i], -M));
        		var.add(cplex.boolVar(column,"d"+i));
        	}
        	
        	int TotalSeparated = 0;
        	boolean change = true;
        	List<Integer> SeparatedCoeff = new ArrayList<Integer>();
        	for(int i = 0; i < MinBoundaryUnsafe.size(); i++)
        		SeparatedCoeff.add(1);
        	
        	int numIter = 0;
            while (change)
            {
            	change = false;
            	IloLinearNumExpr obj = cplex.linearNumExpr();
            	for(int k = 0; k<p+1; k++)
            		obj.addTerm(0, var._array[k]);
            	for(int k=0; k<SeparatedCoeff.size(); k++){
            		obj.addTerm(SeparatedCoeff.get(k), var._array[p+1+k]);
            		//cplex.setLinearCoef(modelObj, 0, arg2);
            		
            	}
            	modelObj.setExpr(obj);
            	//IloLinearNumExpr obj2 = (IloLinearNumExpr) modelObj.getExpr();
            	cplex.objective(modelObj.getSense());
            	
            	//modelObj = cplex.addMaximize(obj);
            	//cplex.setLinearCoef(modelObj, obj);
            	//cplex.exportModel("Linear"+numIter+".lp");
            	cplex.solve();
            	
            	double[] x = new double[p + 1];
                for (int i = 0; i < p+1; i++)
                {
                	IloNumVar elem = var.getElement(i);
                	x[i] = cplex.getValue(elem);
                }
                for (int i = p+1; i < p+1+MinBoundaryUnsafe.size(); i++)
                {
                	IloNumVar elem = var.getElement(i);
                	double d = cplex.getValue(elem);
                	if((SeparatedCoeff.get(i-p-1) == 1) && (d > 0.99))
                	{
                		TotalSeparated++;
                		SeparatedCoeff.set(i-p-1, 0);
                    	change = true;
                	}
                }
                if(TotalSeparated == MinBoundaryUnsafe.size())
                {
                    cplex.end();
                    p = p + r;
                    return true;
                }

                numIter++;
            }
            cplex.end();
           
        }
        catch (Exception e)
        {
            System.out.println("Concert exception caught: " + e);
        }
        p = p + r;
        return false;
    }

    public RAS()
    { 
    }
    
    public RAS(String pn)
    {
        ReadPN(pn);
        // 
        CalculateReachableStates();        
        CalculateReachableSafeStates();
        //RemoveNonboundaryUnsafeStates();
        CalculateMaxSafe();
        //ConvexHull();
        CalculateSafeCount();
        System.out.println("Number of reachable safe states "+this.safeCount);
        System.out.println("Number of maximal safe states "+MaxSafe.size());
        System.out.println("Number of minimal unsafe states "+MinBoundaryUnsafe.size());
        System.out.println("Dim = "+(p-r));
        //printStates();
    }
    void printStates()
    {
    	System.out.println("All States");
    	System.out.println("*************");
    	for(int i=0;i<States.size();i++)
    	{
    		int [] x = States.get(i);
    		System.out.print(i+" : ");
    		for(int j=0;j<p-r;j++)
    			System.out.print(x[j]+",");
    		System.out.print(" || ");
    		if(this.Safe.get(i))
    			System.out.print(" Safe ");
    		else
    			System.out.print(" Unsafe ");
    		System.out.print(" || ");
    		if(this.MaxSafe.contains(i))
    			System.out.print(" Max Safe ");
    		if(this.MinBoundaryUnsafe.contains(i))
    			System.out.print(" Min Unsafe ");
    		
    		System.out.println("");
    	}
    	System.out.println("Reachability");
    	System.out.println("*************");
    	for(int i=0;i<States.size();i++)
    	{
    		System.out.print(i+"-->");
    		for(int j : NextStates.get(i))
    			System.out.print(j+",");
    		System.out.println("");
    	}
    	System.out.println("");
    }
    void printStates2()
    {
    	System.out.println("Maximal safe");
    	System.out.println("*************");
    	for(int i=0;i<States.size();i++)
    	{
    		if(!this.MaxSafe.contains(i))
    			continue;
    		int [] x = States.get(i);
    		System.out.print(i+" : ");
    		for(int j=0;j<p-r;j++)
    			System.out.print(x[j]+",");
    		System.out.println("");
    	}
    	
    	System.out.println("Minimal unsafe");
    	System.out.println("*************");
    	for(int i=0;i<States.size();i++)
    	{
    		if(!this.MinBoundaryUnsafe.contains(i))
    			continue;
    		int [] x = States.get(i);
    		System.out.print(i+" : ");
    		for(int j=0;j<p-r;j++)
    			System.out.print(x[j]+",");
    		System.out.println("");
    	}
    	
    }
    void printMaxSafe()
    {
    	System.out.println("Maximal safe");
    	System.out.println("*************");
    	for(int i=0;i<States.size();i++)
    	{
    		if(!this.MaxSafe.contains(i))
    			continue;
    		int [] x = States.get(i);
    		System.out.print(i+" : ");
    		for(int j=0;j<p-r;j++)
    			System.out.print(x[j]+",");
    		System.out.println("");
    	}
    }

    /// <summary>
    /// copy constructor for deep copying
    /// </summary>
    /// <param name="ras"></param>
    public RAS(RAS ras)
    {
        m0 = null;
        C = null;
        //StateDict.clear();

        Safe = new ArrayList<Boolean>(ras.Safe);
        MaxSafe = new HashSet<Integer>();//ras.MaxSafe
        MinBoundaryUnsafe = new HashSet<Integer>();//ras.MinUnsafe
        parentConvexHullStates = ras.myConvexHullStates;

    }


	@Override
	public int compareTo(RAS arg0) {
		return Integer.compare(arg0.MaxSafe.size(), this.MaxSafe.size());
	}

   

}


