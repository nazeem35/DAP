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

    public List<String> States = new ArrayList<String>();
    public List<Boolean> Safe = new ArrayList<Boolean>();
    public List<Integer> MaxSafe = new ArrayList<Integer>();
    public List<Integer> MinUnsafe = new ArrayList<Integer>();
    public List<Integer> BoundaryUnsafe = new ArrayList<Integer>();
    public List<Integer> ConvexHullStates = new ArrayList<Integer>();
    public List<List<Integer>> NextStates = new ArrayList<List<Integer>>();
    public Map<String, Integer> StateDict = new HashMap<String, Integer>();
    List<List<Integer>> ConflictStages = new ArrayList<List<Integer>>();

    public void CalculateSafeCount()
    {
        safeCount = 0;
        for (int i = 0; i < Safe.size(); i++)
            if (Safe.get(i))
                safeCount++;
    }

    //Ahmed - indexing looks weird. Why?
    public List<Integer> ConvexHull()
    {
    	//return MaxSafe;
    	// return MaxSafe temporarily
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
                String[] tokens = States.get(i).split(",");
                double[] location = new double[p];
                for (int j = 0; j < p; j++)
                    vertices[j][itr] = Double.parseDouble(tokens[j]);
                itr++;
            }
        }
        for (int itr1 = 0; itr1 < NumberOfVertices; itr1++)
        {
            // if it is not max safe do not examine it.
        	//Ahmed not sure if this works or not
            if (!MaxSafe.contains(SafeIDX.get(itr1)))
                continue;
            
            // If the maximal state is on the convex hull of the states before pruning
            // then, it is on the convex hull of the states after pruning.
            if(ConvexHullStates.contains(SafeIDX.get(itr1)))
            {
            	points.add(SafeIDX.get(itr1));
            	continue;
            }

 
            try
            {
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

        //Console.WriteLine("Out of the {0} 6D vertices, there are {1} Voronoi cells and {2} edges.",
        //    NumberOfVertices, voronoi.Vertices.Count(), voronoi.Edges.Count());

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
	        //Ahmed not sure if this works
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
        States.add(join(",", m0));

        while (currentState < States.size())
        {
            //0- Initialize the next states
            List<Integer> next = new ArrayList<Integer>();
            //1- Get the state that you want to explore
            int[] s = new int[p];
            String[] tokens = States.get(currentState).split(",");
            for (int i = 0; i < p; i++)
                s[i] = Integer.parseInt(tokens[i]);
            //2- Make sure that the state doesn't have any stage conflict
            boolean conflict = false;
            for (int j = 0; j < ConflictStages.size(); j++)
            {
                int NonZeroCount = 0;
                for (int k = 0; k < ConflictStages.get(j).size(); k++)
                {
                    if (!tokens[ConflictStages.get(j).get(k)].equals("0"))
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
                            States.add(join(",", m));
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
    /// uses the C matrix and the initial marking to calculate all the reachable states in FromStates list
    /// </summary>
    public void CalculateReachableStates(List<String> FromStates)
    {
        int currentState = 0;
        StateDict.put(join(",", m0), 0);
        States.add(join(",", m0));

        while (currentState < States.size())
        {
            //0- Initialize the next states
            List<Integer> next = new ArrayList<Integer>();
            //1- Get the state that you want to explore
            int[] s = new int[p];
            String[] tokens = States.get(currentState).split(",");
            for (int i = 0; i < p; i++)
                s[i] = Integer.parseInt(tokens[i]);
            //2- Make sure that the state doesn't have any stage conflict
            boolean conflict = false;
            for (int j = 0; j < ConflictStages.size(); j++)
            {
                int NonZeroCount = 0;
                for (int k = 0; k < ConflictStages.get(j).size(); k++)
                {
                    if (! tokens[ConflictStages.get(j).get(k)].equals("0"))
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
                    	if(FromStates.contains(join(",", m)))
                    	{
                            if (!StateDict.containsKey(join(",", m)))
                            {
                                StateDict.put(join(",", m), States.size());
                                States.add(join(",", m));
                            }
                            next.add(StateDict.get(join(",", m)));
                    	}
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
    }

    public void RemoveNonboundaryUnsafeStates()
    {
        CalculateMaxSafe();
        for (int i = States.size() - 1; i >= 0; i--)
        {
            if (BoundaryUnsafe.contains(i))
            {
                NextStates.set(i,new ArrayList<Integer>());
                continue;
            }
            else if (Safe.get(i) == false)
            {
                NextStates.set(i, new ArrayList<Integer>());
                for (int itr = 0; itr < States.size(); itr++)
                {
                	if(NextStates.get(itr).contains(i))
                		NextStates.get(itr).remove(new Integer(i));
                }
                //StateDict.Remove(States[i]);
                States.set(i, "");
            }
        }

        int newidx = States.indexOf("");
        if (newidx == -1)
            return;
        for (int i = States.indexOf(""); i < States.size(); i++)
        {
        	//Ahmed might be problematic
            if (!States.get(i).equals(""))
            {
                States.set(newidx, States.get(i));
                States.set(i, "");
                Safe.set(newidx, Safe.get(i));
                NextStates.set(newidx, new ArrayList<Integer>(NextStates.get(i)));
                //StateDict[States[newidx]] = newidx;

                for (int itr = 0; itr < NextStates.size(); itr++)
                {
                	//Ahmed -- Not sure
                    int index = NextStates.get(itr).indexOf(i);
                    if (index != -1)
                        NextStates.get(itr).set(index, newidx);
                }
                newidx++;
                continue;
            }

        }
        for (int i = States.size() - 1; i > 0; i--)
        {
        	//Ahmed might be problematic
            if (States.get(i) .equals( ""))
            {
            	//Ahmed remove also might be problematic
                States.remove(i);
                NextStates.remove(i);
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

    void getDistinctElements(List<Integer> inputList)
    {
    	Set<Integer> hs = new HashSet<>();
    	hs.addAll(inputList);
    	inputList.clear();
    	inputList.addAll(hs);
    }
    /// <summary>
    /// calculate the maximal safe and the minimal unsafe states
    /// </summary>
    public void CalculateMaxSafe()
    {
        BoundaryUnsafe = new ArrayList<Integer>();
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
        //Ahmed not sure about the order of the array when duplicates are removed
        // Michael, the order is not an issue in the code
        getDistinctElements(BoundaryUnsafe);
        
        //
        MaxSafe = new ArrayList<Integer>();
        MinUnsafe = new ArrayList<Integer>();
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
        
        for(int itr = MaxSafe.size() - 1; itr >= 0; itr--)
        {
        	boolean remove = false;
            String[] tokens1 = States.get(MaxSafe.get(itr)).split(",");

            for (int j = 0; j < MaxSafe.size(); j++)
            {
                if (j == itr)
                    continue;
                boolean AllLessOrEqual = true;
                String[] tokens2 = States.get(MaxSafe.get(j)).split(","); 
                for (int k = 0; k < p - r; k++)
                {
                    if(Integer.parseInt(tokens1[k]) > Integer.parseInt(tokens2[k]))
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
                MaxSafe.remove(itr);
            }
        }

        for (int itr = MinUnsafe.size() - 1; itr >= 0; itr--)
        {
            boolean remove = false;
            String[] tokens1 = States.get(MinUnsafe.get(itr)).split(",");

            for (int j = 0; j < MinUnsafe.size(); j++)
            {
                if (j == itr)
                    continue;
                boolean AllGreaterOrEqual = true;
                String[] tokens2 = States.get(MinUnsafe.get(j)).split(",");
                for (int k = 0; k < p - r; k++)
                {
                    if (Integer.parseInt(tokens1[k]) < Integer.parseInt(tokens2[k]))
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
                MinUnsafe.remove(itr);
            }
        }
    }

//    /// <summary>
//    /// mark one of the states to be unsafe and modify the data accordingly
//    /// </summary>
//    /// <param name="state"></param>
//    public void Prune(int state)
//    {
//        Safe.set(state, false);
//        //check if other states became unsafe
//        boolean change = true;
//        while (change)
//        {
//            change = false;
//            for (int i = 0; i < States.size(); i++)
//            {
//                if (Safe.get(i))
//                {
//                    boolean allfalse = true;
//                    for (int j = 0; j < NextStates.get(i).size(); j++)
//                        if (Safe.get(NextStates.get(i).get(j)))
//                        {
//                            allfalse = false;
//                            break;
//                        }
//                    if (allfalse)
//                    {
//                        Safe.set(i, false);
//                        change = true;
//                    }
//                }
//            }
//        }
//        //recalculate the max safe and min unsafe
//        RemoveNonboundaryUnsafeStates();
//        CalculateMaxSafe();
//        CalculateSafeCount();
//    }

    /// <summary>
    /// check whether the maximal safe and minimal unsafe are linearly separable or not.
    /// </summary>
    /// <returns></returns>
    public boolean LinearSpearable()
    {
        CalculateMaxSafe();
        p = p-r;
        while (MinUnsafe.size() > 0)
        {
            double[] ab = SolveMIP412();
            int totalRemoved = 0;
            for (int i = MinUnsafe.size() - 1; i >= 0; i--)
            {
                String[] y = States.get(MinUnsafe.get(i)).split(",");
                double sum = 0;
                for (int j = 0; j < p; j++)
                    sum += ab[j] * Integer.parseInt(y[j]);
                if (sum > ab[p])
                {
                    MinUnsafe.remove(i);
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
        		 for (int i = 0; i < MaxSafe.size(); i++)
        		 {
        			 String[] x = States.get(MaxSafe.get(i)).split(",");
        			 if(!x[j].equals("0"))
        				 column = column.and(cplex.column(rng[0][i], Integer.parseInt(x[j])));
        		 }
        		 for (int i = 0; i < MinUnsafe.size(); i++)
        		 {
        			 String[] x = States.get(MinUnsafe.get(i)).split(",");
        			 if(!x[j].equals("0"))
        				 column = column.and(cplex.column(rng[1][i], Integer.parseInt(x[j])));
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

    public RAS()
    { 
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
//    public RAS(RAS ras)
//    {
//        p = ras.p;
//        r = ras.r;
//        t = ras.t;
//        //empyt m0 (not needed)
//        m0 = null;
//        //m0 = new int[p];
//        //for (int i = 0; i < p; i++)
//        //    m0[i] = ras.m0[i];
//        //empty C (not needed)
//        C = null;
//        //C = new int[p, t];
//        //for (int i = 0; i < p; i++)
//        //    for (int j = 0; j < t; j++)
//        //        C[i, j] = ras.C[i, j];///
//
//        States = new ArrayList<String>(ras.States);
//        Safe = new ArrayList<Boolean>(ras.Safe);
//        MaxSafe = new ArrayList<Integer>(ras.MaxSafe);
//        MinUnsafe = new ArrayList<Integer>(ras.MinUnsafe);
//        //NextStates = ras.NextStates.Select(x => x.ToList()).ToList();
//        NextStates = new ArrayList<List<Integer>>();
//        //empty dict (not need)
//        StateDict.clear();// = new Dictionary<String, int>();
//
//    }

    /// <summary>
    /// copy constructor for deep copying that implements pruning function
    /// </summary>
    /// <param name="ras"></param>
    public RAS(RAS ras, List<Integer> CH, int itr)
    {
        p = ras.p;
        r = ras.r;
        t = ras.t;
        m0 = new int[p];
        for (int i = 0; i < p; i++)
            m0[i] = ras.m0[i];
        C = new int[p][t];
        for (int i = 0; i < p; i++)
        {
            for (int j = 0; j < t; j++)
                C[i][j] = ras.C[i][j];
        }
        
        for(int i = 0; i < ras.ConflictStages.size(); i++)
        {
        	List<Integer> temp = new ArrayList<Integer>(ras.ConflictStages.get(i));
        	ConflictStages.add(temp);
        }

        List<String> temp = new ArrayList<String>(ras.States);
        temp.remove((int)CH.get(itr));
        CalculateReachableStates(temp);        
        CalculateReachableSafeStates();
        RemoveNonboundaryUnsafeStates();
        CalculateMaxSafe();
        CalculateSafeCount();
        
        for(int i = 0; i < CH.size(); i++)
        {
        	int index = States.indexOf(ras.States.get((int) CH.get(i)));
        	if(index >= 0)
        	{
        		ConvexHullStates.add(index);
        	}
        }

    }

	@Override
	public int compareTo(RAS arg0) {
		return Integer.compare(arg0.safeCount, this.safeCount);
	}

   

}


