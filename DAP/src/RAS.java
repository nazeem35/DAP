import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.Reader;
import java.io.Writer;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import ilog.concert.*;
import ilog.concert.IloCopyManager.Check;
import ilog.cplex.*;

public class RAS implements Comparable<RAS>
{
    public int p;
    public int t;
    public int r;
    public int[] m0;
    public int[][] C;
    public int safeCount;

    public List<int []> States = new ArrayList<int []>();
    public List<Boolean> Safe = new ArrayList<Boolean>();
    public HashSet<Integer> MaxSafe = new HashSet<Integer>();
    public HashSet<Integer> MinUnsafe = new HashSet<Integer>();
    public HashSet<Integer> BoundaryUnsafe = new HashSet<Integer>();
    public HashSet <Integer> ParentConvexHullStates = new HashSet <Integer>();
    public List<List<Integer>> NextStates = new ArrayList<List<Integer>>();
    public List<List<Integer>> PreviousStates = new ArrayList<List<Integer>>();
    public Map<String, Integer> StateDict = new HashMap<String, Integer>();
    List<List<Integer>> ConflictStages = new ArrayList<List<Integer>>();

    public void CalculateSafeCount()
    {
        safeCount = 0;
        for (int i = 0; i < Safe.size(); i++)
            if (Safe.get(i))
                safeCount++;
    }

    public List<Integer> ConvexHull()
    {
    	List<Integer> points = new ArrayList<Integer>();
        List<Integer> SafeIDX = new ArrayList<Integer>();
        int NumberOfVertices = 0;
        for (int i = 0; i < Safe.size(); i++)
        {
            if (Safe.get(i))
            {
                NumberOfVertices++;
                SafeIDX.add(i);
            }
        }

        double[][] vertices = new double[p] [NumberOfVertices];
        int itr = 0;
        for (int i = 0; i < States.size(); i++)
        {
            if (Safe.get(i))
            {
                for (int j = 0; j < p; j++)
                    vertices[j][itr] = States.get(i)[j];
                itr++;
            }
        }
        for (int MSstate : MaxSafe)
        {
            // If the maximal state is on the convex hull of the states before pruning
            // then, it is on the convex hull of the states after pruning.
            if(ParentConvexHullStates.contains(MSstate))
            {
            	points.add(MSstate);
            	continue;
            }

 
            try
            {
            	//The index of the state that we are considering from the set of safe states
            	int itr1 = SafeIDX.indexOf(MSstate);
            	
                
            	IloCplex cplex = new IloCplex();
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

        ParentConvexHullStates.addAll(points);
        
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
            List<Integer> next = new ArrayList<Integer>();
            //1- Get the state that you want to explore
            //Ahmed -- No need to allocate and copy another array
            int [] s = States.get(currentState);
            /*
            int[] s = new int[p];
            for (int i = 0; i < p; i++)
                s[i] = States.get(currentState)[i];*/
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
                    	//Ahmed -- No need to call join multiple times
                    	String str_m = join(",", m);
                        if (!StateDict.containsKey(str_m))
                        {
                            StateDict.put(str_m, States.size());
                            States.add(m);
                        }
                        //Ahmed No need to call the hashmap
                        next.add(States.size()-1);
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
                    for (int j = 0; j < NextStates.get(i).size(); j++)
                        if (Safe.get(NextStates.get(i).get(j)))
                        {
                            change = true;
                            Safe.set(i, true);
                        }
                }
            }

        }

        for(int i = 0; i < States.size(); i++)
        {
        	List<Integer> temp = new ArrayList<Integer>();
        	PreviousStates.add(temp);
        }
        for(int i = 0; i < NextStates.size(); i++)
        {
        	for(int j = 0; j < NextStates.get(i).size(); j++)
        	{
        		PreviousStates.get(NextStates.get(i).get(j)).add(i);
        	}
        }
    }

    public void RemoveNonboundaryUnsafeStates()
    {
        CalculateMaxSafe();
        for (int i = States.size() - 1; i >= 0; i--)
        {
            if (BoundaryUnsafe.contains(i))
            {
                NextStates.set(i,new ArrayList<Integer>());
                PreviousStates.set(i,new ArrayList<Integer>());
                continue;
            }
            else if (Safe.get(i) == false)
            {
                NextStates.set(i, new ArrayList<Integer>());
                PreviousStates.set(i, new ArrayList<Integer>());
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
                NextStates.set(newidx, new ArrayList<Integer>(NextStates.get(i)));
                PreviousStates.set(newidx, new ArrayList<Integer>(PreviousStates.get(i)));
                //StateDict[States[newidx]] = newidx;

                for (int itr = 0; itr < NextStates.size(); itr++)
                {
                	//Ahmed -- Not sure
                    int index = NextStates.get(itr).indexOf(i);
                    if (index != -1)
                        NextStates.get(itr).set(index, newidx);
                    
                    index = PreviousStates.get(itr).indexOf(i);
                    if (index != -1)
                        PreviousStates.get(itr).set(index, newidx);
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


    }


	// Commenting all the code for the new pruning function
    //public void RemoveResourcesFromStates()
    //{
        //p = p - r;
        //for (int itr = 0; itr < States.size(); itr++)
        //{
        //    String[] tokens = States.get(itr).split(",");
        //    String newstate = tokens[0];
        //    for (int i = 1; i < p; i++)
        //        newstate += "," + tokens[i];
        //    States.set(itr, newstate);
        //}
    //}

    
    /// <summary>
    /// calculate the maximal safe and the minimal unsafe states
    /// </summary>
    public void CalculateMaxSafe()
    {
        BoundaryUnsafe = new HashSet<Integer>();
        for (int i = 0; i < States.size(); i++)
        {
            if (Safe.get(i))
            {
                for (int j = 0; j < NextStates.get(i).size(); j++)
                {
                    if (!Safe.get(NextStates.get(i).get(j)))
                    {
                        BoundaryUnsafe.add(NextStates.get(i).get(j));
                    }
                }
            }
        }
        
        //
        MaxSafe = new HashSet<Integer>();
        MinUnsafe = new HashSet<Integer>();
        for(int i = 0; i < States.size(); i++)
        {
            if(Safe.get(i))
            {
                MaxSafe.add(i);
            }
            else
            {
                MinUnsafe.add(i);
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

        Object[] array = MinUnsafe.toArray();
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
                MinUnsafe.remove((int)array[itr]);
            }
        }
    }

    /// <summary>
    /// mark one of the states to be unsafe and modify the data accordingly
    /// </summary>
    /// <param name="state"></param>
    public void Prune(int PrunedState, RAS Parent)
    {
        /*Safe.set(state, false);
        //check if other states became unsafe
        boolean change = true;
        while (change)
        {
            change = false;
            for (int i = 0; i < States.size(); i++)
            {
                if (Safe.get(i))
                {
                    boolean allfalse = true;
                    for (int j = 0; j < NextStates.get(i).size(); j++)
                        if (Safe.get(NextStates.get(i).get(j)))
                        {
                            allfalse = false;
                            break;
                        }
                    if (allfalse)
                    {
                        Safe.set(i, false);
                        change = true;
                    }
                }
            }
        }*/
    	
    	// lines 1-4 of the algorithm
    	//The set S will contains all the states s such that s <= s'' for s'' \in \bar{S} (the maximal of the parent) except the pruned state
       	HashSet<Integer> S = new HashSet<Integer>();
    	for(int i = 0; i < States.size(); i++)
    	{
    		if(i == PrunedState)
    			continue;
    		
    		int [] state = States.get(i);
    		for(int MSstate : Parent.MaxSafe)
    		{
    			int[] MaxState = States.get(MSstate);
    			boolean AllLess = true;
    			for(int k = 0; k < p-r; k++)
    			{
    				if(state[k] > MaxState[k])
    				{
    					AllLess = false;
    					break;
    				}
    			}
    			if(AllLess)
    			{
    				S.add(i);
    				break;
    			}
    		}
    	}
    	HashSet<Integer> Shat_r = new HashSet<Integer>();
    	Shat_r.add(0);
    	boolean change = true;
    	while(change)
    	{
    		change = false;
    		Object[] array = S.toArray();
    		for(int i = 0; i < array.length; i++)
    		{
    			for(int j = 0; j < PreviousStates.get((int) array[i]).size(); j++)
    			{
    				if(Shat_r.contains(PreviousStates.get((int) array[i]).get(j)))
    				{
    					Shat_r.add((int) array[i]);
    					S.remove((int) array[i]);
    					change = true;
    					break;
    				}
    			}
    		}
    	}
    	// line 5-7 of the algorithm
    	change = true;
    	while(change)
    	{
    		change = false;
    		Object[] array = Shat_r.toArray();
    		for(int i = 0; i < array.length; i++)
    		{
        		boolean AllOut = true;
    			for(int j = 0; j < NextStates.get((int) array[i]).size(); j++)
    			{
    				if(Shat_r.contains(NextStates.get((int) array[i]).get(j)))
    				{
    					AllOut = false;
    					break;
    				}
    			}
    			if(AllOut)
    			{
    				Shat_r.remove((int) array[i]);
    				change = true;
    			}
    		}
    	}
    	for(int i = 0; i < Safe.size(); i++)
    		Safe.set(i,  false);
    	for(int i : Shat_r)
    		Safe.set(i, true);
    	// line 8 of the algorithm
        CalculateMaxSafe(); 
        // This calculates the number of safe states
        CalculateSafeCount();
    }

    /// <summary>
    /// check whether the maximal safe and minimal unsafe are linearly separable or not.
    /// </summary>
    /// <returns></returns>
    public boolean LinearSpearable()
    {
        //CalculateMaxSafe();
        p = p-r;
        while (MinUnsafe.size() > 0)
        {
            double[] ab = SolveMIP412();
            int totalRemoved = 0;
            Object[] array = MinUnsafe.toArray();
            for (int i = 0; i < array.length; i++)
            {
                int[] y = States.get((int)array[i]);
                double sum = 0;
                for (int j = 0; j < p; j++)
                    sum += ab[j] * y[j];
                if (sum > ab[p])
                {
                    MinUnsafe.remove((int)array[i]);
                    totalRemoved++;
                }
            }
            if (totalRemoved == 0)
            {
            	p = p + r;
                return false;
            }

        }
        p = p + r;
        return true;
    }
    
    /*public boolean LinearSpearable()
    {
    	p = p - r;
        //Ahmed -- M can be set to p * max val in states
        double M = 1000;
        double eps = 0.0001;
        // Solve the MIP from the file
        try
        {
            IloCplex cplex = new IloCplex();
            IloObjective modelObj = cplex.addMaximize();
        	IloRange [][] rng = new IloRange[2][];
        	rng[0] = new IloRange[MaxSafe.size()];
        	rng[1] = new IloRange[MinUnsafe.size()];
        	for (int i = 0; i < MaxSafe.size(); i++)
        		rng[0][i] = cplex.addRange(Double.MAX_VALUE*-1,0, "Safe"+i);
        	for (int i = 0; i < MinUnsafe.size(); i++)
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
        		 for (int MinUnsafe : MinUnsafe)
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
        	for (int i = 0; i < MinUnsafe.size(); i++)
        		columnB = columnB.and(cplex.column(rng[1][i], -1));
        	 var.add(cplex.numVar(columnB, 0., 1 ,"b"));
        	//Indicators for separation
        	for (int i = 0; i < MinUnsafe.size(); i++)
        	{
        		IloColumn column = cplex.column(modelObj, 1);
        		column = column.and(cplex.column(rng[1][i], -M));
        		var.add(cplex.boolVar(column,"d"+i));
        	}
        	
        	int TotalSeparated = 0;
        	boolean change = true;
        	List<Integer> SeparatedCoeff = new ArrayList<Integer>();
        	for(int i = 0; i < MinUnsafe.size(); i++)
        		SeparatedCoeff.add(1);
        	
            while (change)
            {
            	change = false;
            	IloLinearNumExpr obj = cplex.linearNumExpr();
            	for(int k=0; k<SeparatedCoeff.size(); k++){
            		obj.addTerm(SeparatedCoeff.get(k), cplex.boolVar("d"+k));
            	}
            	modelObj.setExpr(obj);
            	
            	cplex.solve();
            	double[] x = new double[p + 1];
                for (int i = 0; i < p+1; i++)
                {
                	IloNumVar elem = var.getElement(i);
                	x[i] = cplex.getValue(elem);
                }
                for (int i = p+1; i < p+1+MinUnsafe.size(); i++)
                {
                	IloNumVar elem = var.getElement(i);
                	double d = cplex.getValue(elem);
                	if(d == 1)
                	{
                		TotalSeparated++;
                		//IloLinearNumExpr  temp = (IloLinearNumExpr) modelObj.getExpr();//.set.setExpr(modelObj.getExpr().toString().replace("+ 1.0*d" + (i-p-1), ""));
                		//modelObj.clearExpr();
                		//modelObj = cplex.addMaximize();

                		SeparatedCoeff.set(i-p-1, 0);
                    	change = true;
                	}
                }
                if(TotalSeparated == MinUnsafe.size())
                {
                    cplex.end();
                    p = p + r;
                    return true;
                }


            }
            cplex.end();
           
        }
        catch (Exception e)
        {
            System.out.println("Concert exception caught: " + e);
        }
        p = p + r;
        return false;
    }*/

    public double[] SolveMIP412()
    {
        //Ahmed -- M can be set to p * max val in states
        double M = 1000;
        double eps = 0.0001;
        // Solve the MIP from the file
        try
        {
            IloCplex cplex = new IloCplex();
            IloObjective modelObj = cplex.addMaximize();
        	IloRange [][] rng = new IloRange[2][];
        	rng[0] = new IloRange[MaxSafe.size()];
        	rng[1] = new IloRange[MinUnsafe.size()];
        	for (int i = 0; i < MaxSafe.size(); i++)
        		rng[0][i] = cplex.addRange(Double.MAX_VALUE*-1,0, "Safe"+i);
        	for (int i = 0; i < MinUnsafe.size(); i++)
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
        		 for (int MinUnsafe : MinUnsafe)
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
        	for (int i = 0; i < MinUnsafe.size(); i++)
        		columnB = columnB.and(cplex.column(rng[1][i], -1));
        	 var.add(cplex.numVar(columnB, 0., 1 ,"b"));
        	//Indicators for separation
        	for (int i = 0; i < MinUnsafe.size(); i++)
        	{
        		IloColumn column = cplex.column(modelObj, 1);
        		column = column.and(cplex.column(rng[1][i], -M));
        		var.add(cplex.boolVar(column,"d"+i));
        	}
        	
            if (cplex.solve())
            {
                //MessageBox.Show("Solution status = " + cplex.GetStatus());
                //MessageBox.Show("Solution value  = " + cplex.ObjValue);

                // access ILPMatrix object that has been read from file in order to
                // access variables which are the columns of the lp.  Method
                // importModel guarantees to the model into exactly on ILPMatrix
                // object which is why there are no test or iterations needed in the
                // following line of code.

               
                double[] x = new double[p + 1];
                for (int i = 0; i < p+1; i++)
                {
                	IloNumVar elem = var.getElement(i);
                	x[i] = cplex.getValue(elem);
                }
                
                cplex.end();
                return x;

            }
            cplex.end();
           
        }
        catch (Exception e)
        {
            System.out.println("Concert exception caught: " + e);
        }
        return new double[p + 1];
    }

   
    
    public RAS(String pn)
    {
        ReadPN(pn);
        // 
        CalculateReachableStates();        
        CalculateReachableSafeStates();
        RemoveNonboundaryUnsafeStates();
        CalculateMaxSafe();
        //ConvexHull();
        CalculateSafeCount();
    }

    /// <summary>
    /// copy constructor for deep copying
    /// </summary>
    /// <param name="ras"></param>
    public RAS(RAS parentRAS)
    {
        p = parentRAS.p;
        r = parentRAS.r;
        t = parentRAS.t;
        //empyt m0 (not needed)
        m0 = null;
        C = null;

        //Ahmed Copy constructor for RAS: no need to create new lists
        States = parentRAS.States;
        Safe = parentRAS.Safe;
        NextStates = parentRAS.NextStates;
        PreviousStates = parentRAS.PreviousStates;
        StateDict = parentRAS.StateDict;
        
        
        MaxSafe = new HashSet<Integer>();//ras.MaxSafe
        MinUnsafe = new HashSet<Integer>();//ras.MinUnsafe
        //NextStates = ras.NextStates.Select(x => x.ToList()).ToList();
       
        
        //empty dict (not need)
       

    }


	@Override
	public int compareTo(RAS arg0) {
		return Integer.compare(arg0.safeCount, this.safeCount);
	}

   

}


