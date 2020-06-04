import java.io.BufferedReader;
import java.io.BufferedWriter;
//import java.io.BufferedWriter;
//import java.io.FileInputStream;
//import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
//import java.io.InputStream;
//import java.io.InputStreamReader;
//import java.io.OutputStreamWriter;
//import java.io.Reader;
//import java.io.Writer;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.LinkedList;
import java.util.Map;
import java.util.Queue;
//import java.util.Set;
import java.util.Stack;

import ilog.concert.*;
//import ilog.concert.IloCopyManager.Check;
import ilog.cplex.*;
import java.lang.Math; 


public class RAS implements Comparable<RAS> {
	public static double eps = 0.0001;
	public static int p;
	public static int t;
	public static int r;
	public static int[] m0;
	public static int[][] C;
	public int safeCount;
	public static int lp1cnt;
	public static int lp2cnt;
	public static IloCplex cplex3;
	public static IloLPMatrix matrix3;
	public static IloCplex cplex2;
	public static IloLPMatrix matrix2;
	public static IloObjective modelObj2;
	public static int columnsCount2 = 0;
	public static IloNumVarArray var2;
	public static IloCplex cplex;

	public static List<int[]> States = new ArrayList<int[]>();
	public List<Boolean> Safe = new ArrayList<Boolean>();
	public HashSet<Integer> MaxSafe = new HashSet<Integer>();
	public HashSet<Integer> MinBoundaryUnsafe = new HashSet<Integer>();
	public HashSet<Integer> MinBoundaryUnsafeUnseparable = new HashSet<Integer>();
	// public HashSet<Integer> BoundaryUnsafe = new HashSet<Integer>();
	public HashSet<Integer> myConvexHullStates = new HashSet<Integer>();
	public HashSet<Integer> parentConvexHullStates = null;
	public static List<HashSet<Integer>> NextStates = new ArrayList<HashSet<Integer>>();
	public static List<HashSet<Integer>> PreviousStates = new ArrayList<HashSet<Integer>>();
	public static Map<String, Integer> StateDict = new HashMap<String, Integer>();
	static HashSet<Integer> nonBoundayUnsafe = new HashSet<Integer>();
	static HashMap<Integer, HashSet<Integer>> dominatedBy = new HashMap<Integer, HashSet<Integer>>();
	public static List<IloLinearNumExpr> linear_sep_constraints = new ArrayList<IloLinearNumExpr>();
	public int max_num_constraints2;
	public int max_num_constraints3;
	int prunedState;
	RAS parentRAS = null;
	int[] unsafe_row_idx;
	int[] unsafe_col_idx ;
	double[] unsafe_val ;
	char[] joinHelper;
	char [][]joinIntHelper;
	int joinHelper_size;
	int joinIntHelper_size;

	@Override
	public String toString() {
		String ras = "" + safeCount + ",";
		ras += Safe.size() + ",";
		for (int i = 0; i < Safe.size(); i++)
			ras += Safe.get(i) + ",";
		ras += MaxSafe.size() + ",";
		for (int i : MaxSafe)
			ras += i + ",";

		ras += MinBoundaryUnsafe.size() + ",";
		for (int i : MinBoundaryUnsafe)
			ras += i + ",";
		ras += MinBoundaryUnsafeUnseparable.size() + ",";
		for (int i : MinBoundaryUnsafeUnseparable)
			ras += i + ",";
		ras += myConvexHullStates.size() + ",";
		for (int i : myConvexHullStates)
			ras += i + ",";
		ras += parentConvexHullStates.size() + ",";
		for (int i : parentConvexHullStates)
			ras += i + ",";
		ras += nonBoundayUnsafe.size() + ",";
		for (int i : nonBoundayUnsafe)
			ras += i + ",";

		ras += dominatedBy.size() + ",";
		for (Map.Entry<Integer, HashSet<Integer>> kv : dominatedBy.entrySet()) {
			int key = kv.getKey();
			HashSet<Integer> value = kv.getValue();
			ras += key + ",";
			ras += value.size() + ",";
			for (int i : value)
				ras += i + ",";
		}

		return ras;
	}

	public void WriteAsALine(BufferedWriter writer) {
		try {
			writer.write("" + safeCount + ",");
			writer.write(Safe.size() + ",");
			for (int i = 0; i < Safe.size(); i++)
				writer.write(Safe.get(i) + ",");
			writer.write(MaxSafe.size() + ",");
			for (int i : MaxSafe)
				writer.write(i + ",");

			writer.write(MinBoundaryUnsafe.size() + ",");
			for (int i : MinBoundaryUnsafe)
				writer.write(i + ",");
			writer.write(MinBoundaryUnsafeUnseparable.size() + ",");
			for (int i : MinBoundaryUnsafeUnseparable)
				writer.write(i + ",");
			writer.write(myConvexHullStates.size() + ",");
			for (int i : myConvexHullStates)
				writer.write(i + ",");
			writer.write(parentConvexHullStates.size() + ",");
			for (int i : parentConvexHullStates)
				writer.write(i + ",");
			writer.write(nonBoundayUnsafe.size() + ",");
			for (int i : nonBoundayUnsafe)
				writer.write(i + ",");

			writer.write(dominatedBy.size() + ",");
			for (Map.Entry<Integer, HashSet<Integer>> kv : dominatedBy.entrySet()) {
				int key = kv.getKey();
				HashSet<Integer> value = kv.getValue();
				writer.write(key + ",");
				writer.write(value.size() + ",");
				for (int i : value)
					writer.write(i + ",");
			}
			writer.newLine();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	// NA only to differ between the other constructor
	public RAS(String ras, int NA) {
		parentConvexHullStates = new HashSet<Integer>();
		String[] tokens = ras.split(",");
		int itr = 0;
		safeCount = Integer.parseInt(tokens[itr]);
		itr++;
		int size = Integer.parseInt(tokens[itr]);
		itr++;
		for (int i = 0; i < size; i++) {
			Safe.add(Boolean.parseBoolean(tokens[itr]));
			itr++;
		}
		size = Integer.parseInt(tokens[itr]);
		itr++;
		for (int i = 0; i < size; i++) {
			MaxSafe.add(Integer.parseInt(tokens[itr]));
			itr++;
		}

		size = Integer.parseInt(tokens[itr]);
		itr++;
		for (int i = 0; i < size; i++) {
			MinBoundaryUnsafe.add(Integer.parseInt(tokens[itr]));
			itr++;
		}
		size = Integer.parseInt(tokens[itr]);
		itr++;
		for (int i = 0; i < size; i++) {
			MinBoundaryUnsafeUnseparable.add(Integer.parseInt(tokens[itr]));
			itr++;
		}
		size = Integer.parseInt(tokens[itr]);
		itr++;
		for (int i = 0; i < size; i++) {
			myConvexHullStates.add(Integer.parseInt(tokens[itr]));
			itr++;
		}
		size = Integer.parseInt(tokens[itr]);
		itr++;
		for (int i = 0; i < size; i++) {
			parentConvexHullStates.add(Integer.parseInt(tokens[itr]));
			itr++;
		}
		size = Integer.parseInt(tokens[itr]);
		itr++;
		for (int i = 0; i < size; i++) {
			nonBoundayUnsafe.add(Integer.parseInt(tokens[itr]));
			itr++;
		}

		size = Integer.parseInt(tokens[itr]);
		itr++;
		for (int i = 0; i < size; i++) {
			Integer key = Integer.parseInt(tokens[itr]);
			itr++;
			int vsize = Integer.parseInt(tokens[itr]);
			itr++;
			HashSet<Integer> value = new HashSet<Integer>();
			for (int j = 0; j < vsize; j++) {
				value.add(Integer.parseInt(tokens[itr]));
				itr++;
			}
			dominatedBy.put(key, value);
		}

		init_cplex();
	}

	public void CalculateSafeCount() {
		safeCount = 0;
		for (int i = 0; i < Safe.size(); i++)
			if (Safe.get(i))
				safeCount++;
	}

	public HashSet<Integer> RemoveLinearSeparable(List<Integer> SafeSet, HashSet<Integer> SafeSubset, int MinUnsafe) {
		HashSet<Integer> NewSafeSubset = new HashSet<Integer>();

		try {
			cplex = new IloCplex();
			{
				cplex.setParam(IloCplex.IntParam.AdvInd, 0);

				cplex.setOut(null);
				IloObjective modelObj = cplex.addMaximize();
				IloRange[] rng = new IloRange[SafeSet.size()];

				for (int i = 0; i < SafeSet.size(); i++)
					rng[i] = cplex.addRange(Double.MAX_VALUE * -1, 0, "Safe" + i);
				IloNumVarArray var = new IloNumVarArray();
				// Hyerplane coefficients
				for (int j = 0; j < p; j++) {
					IloColumn column = cplex.column(modelObj, 0);
					int itr = 0;
					for (int MSsafe : SafeSet) {
						int[] x = States.get(MSsafe);
						if (x[j] != 0)
							column = column.and(cplex.column(rng[itr], x[j]));
						itr++;
					}
					var.add(cplex.numVar(column, 0., 1, "a" + j));
				}
				// Intercept
				IloColumn columnB = cplex.column(modelObj, 0);
				for (int i = 0; i < SafeSet.size(); i++)
					columnB = columnB.and(cplex.column(rng[i], -1));
				var.add(cplex.numVar(columnB, 0., 1, "b"));

				IloLinearNumExpr exprNew = cplex.linearNumExpr();

				int[] x = States.get(MinUnsafe);
				for (int j = 0; j < p; j++)
					if (x[j] != 0)
						exprNew.addTerm(x[j], var._array[j]);

				exprNew.addTerm(-1, var._array[p]);

				IloRange myConstraint = cplex.addGe(exprNew, eps, "UnsafeState");

				for (int MaxSafe : SafeSubset) {
					// delete the constraint corresponding to a certain state in the safe subset
					int index = SafeSet.indexOf(MaxSafe);
					cplex.remove(rng[index]);
					cplex.clearCuts();
					// check if the unsafe state is linearly separable
					if (cplex.solve()) {
						NewSafeSubset.add(MaxSafe);
					} else {
						// NewSafeSubset.add(MaxSafe);
					}
					// add the constraint
					cplex.add(rng[index]);
					cplex.clearCuts();

				}
			}

			cplex.clearLazyConstraints();
			cplex.clearCallbacks();
			cplex.clearCuts();
			cplex.clearModel();
			cplex.deleteNames();
			cplex.endModel();
			cplex.end();
			cplex = null;

		} catch (Exception e) {
			System.out.println("Concert exception caught: " + e);
		}

		return NewSafeSubset;
	}

	public static HashMap<Integer, Double> sortByValue(HashMap<Integer, Double> hm) {
		// Create a list from elements of HashMap
		List<Map.Entry<Integer, Double>> list = new LinkedList<Map.Entry<Integer, Double>>(hm.entrySet());

		// Sort the list
		Collections.sort(list, new Comparator<Map.Entry<Integer, Double>>() {
			public int compare(Map.Entry<Integer, Double> o1, Map.Entry<Integer, Double> o2) {
				return (o1.getValue()).compareTo(o2.getValue());
			}
		});

		// put data from sorted list to hashmap
		HashMap<Integer, Double> temp = new LinkedHashMap<Integer, Double>();
		for (Map.Entry<Integer, Double> aa : list) {
			temp.put(aa.getKey(), aa.getValue());
		}
		return temp;
	}

	public List<Integer> ConvexHull() {
		// System.out.println("Entered Convex Hull");
		p = p - r;
		List<Integer> points = new ArrayList<Integer>();
		//// List<Integer> points = new ArrayList<Integer>(MaxSafe);
		List<Integer> SafeIDX = new ArrayList<Integer>();
		int NumberOfVertices = MaxSafe.size();
		// Why do we need zero
		// SafeIDX.add(0);
		for (int i : MaxSafe) {
			SafeIDX.add(i);
		}

		double[][] vertices = new double[p][NumberOfVertices];
		for (int i = 0; i < SafeIDX.size(); i++) {
			int[] x = States.get(SafeIDX.get(i));
			for (int j = 0; j < p; j++)
				vertices[j][i] = x[j];
		}
		long startTime = System.currentTimeMillis();
		lp1cnt += MaxSafe.size();
		try {

			cplex = new IloCplex();
			{
				cplex.setOut(null);
				IloObjective modelObj = cplex.addMaximize();
				IloRange[] rng = new IloRange[p + 1];
				for (int j = 0; j < p; j++)
					rng[j] = cplex.addRange(0, 0, "coverDim" + j);
				rng[p] = cplex.addRange(1, 1, "convex");
				IloNumVarArray var = new IloNumVarArray();
				for (int i = 0; i < NumberOfVertices; i++) {
					IloColumn column;
					column = cplex.column(modelObj, 1);

					for (int j = 0; j < p; j++)
						column = column.and(cplex.column(rng[j], vertices[j][i]));
					column = column.and(cplex.column(rng[p], 1));
					var.add(cplex.numVar(column, 0., 1, "h" + i));
				}
				// cplex.exportModel("convex"+Integer.toString(itr1)+".lp");

				int counter = 0;

				for (int MSstate : MaxSafe) {

					// If the maximal state is on the convex hull of the states before pruning
					// then, it is on the convex hull of the states after pruning.
					if (parentConvexHullStates != null && parentConvexHullStates.contains(MSstate)) {
						points.add(MSstate);
						continue;
					}
					// The index of the state that we are considering from the set of safe states
					int itr1 = SafeIDX.indexOf(MSstate);
					for (int j = 0; j < p; j++)
						rng[j].setBounds(vertices[j][itr1], vertices[j][itr1]);
					cplex.setLinearCoef(modelObj, var.getElement(itr1), 0);
					cplex.setParam(IloCplex.IntParam.RootAlg, IloCplex.Algorithm.Dual);
					if (cplex.solve()) {
						double objective = cplex.getObjValue();
						if (objective < eps) // On the boundary
							points.add(SafeIDX.get(itr1));
						else // Suppress
							var.getElement(itr1).setUB(0);
					}
					cplex.setLinearCoef(modelObj, var.getElement(itr1), 1);

				}
			}
			cplex.clearLazyConstraints();
			cplex.clearCallbacks();
			cplex.clearCuts();
			cplex.clearModel();
			cplex.deleteNames();
			cplex.endModel();
			cplex.end();
			cplex = null;

		} catch (Exception e) {
			System.out.println("Concert exception caught: " + e);
		}
		myConvexHullStates.addAll(points);
		// p = p + r;
		long endTime = System.currentTimeMillis();
		// System.out.println("Convex Hull time = "+(endTime-startTime));
		// return points;
		/////////////////////////////////////////////////////////////////////////////////////////////////////////////
		// Only return the convex hull states that are in the convex hull of the minimal
		// states
		/////////////////////////////////////////////////////////////////////////////////////////////////////////////

		HashMap<Integer, Double> pointsReduced = new HashMap<Integer, Double>();

		double MaxObjective = 1000000;

		NumberOfVertices = points.size();
		vertices = new double[p][NumberOfVertices];
		for (int i = 0; i < points.size(); i++) {
			int[] x = States.get(points.get(i));
			for (int j = 0; j < p; j++)
				vertices[j][i] = x[j];
		}

		// for(int MinState : MinBoundaryUnsafe)
		for (int MinState : MinBoundaryUnsafeUnseparable) {
			try {
				cplex = new IloCplex();
				{
					cplex.setOut(null);
					cplex.setParam(IloCplex.DoubleParam.TiLim, 60);
					cplex.setWarning(null);
					IloObjective modelObj = cplex.addMaximize();
					IloRange[] rng = new IloRange[p + 1];

					for (int j = 0; j < p; j++)
						rng[j] = cplex.addRange(States.get(MinState)[j], Double.MAX_VALUE, "coverDim" + j);
					rng[p] = cplex.addRange(0, 1, "convex");
					IloNumVarArray var = new IloNumVarArray();
					for (int i = 0; i < NumberOfVertices; i++) {
						IloColumn column = cplex.column(modelObj, 1);

						for (int j = 0; j < p; j++)
							column = column.and(cplex.column(rng[j], vertices[j][i]));

						column = column.and(cplex.column(rng[p], 1));

						var.add(cplex.numVar(column, 0., 1, "h" + i));
					}

					int currItr = 0;
					boolean change = true;
					while (change) {
						change = false;
						lp2cnt++;

						if (cplex.solve()) {
							double objective = cplex.getObjValue();

							if (objective > eps)// the min unsafe is a combination of max unsafe
							{
								change = true;

								double[] x = new double[NumberOfVertices];
								for (int i = 0; i < NumberOfVertices; i++) {
									IloNumVar elem = var.getElement(i);
									x[i] = cplex.getValue(elem);
								}

								// HashSet<Integer> SafeSubset = new HashSet<Integer>();
								// for (int i = 0; i < NumberOfVertices; i++)
								// {
								// if(x[i] > 0)
								// {
								// SafeSubset.add(points.get(i));
								// }
								// }
								// HashSet<Integer> NewSubset = RemoveLinearSeparable(points, SafeSubset,
								// MinState);

								for (int i = 0; i < NumberOfVertices; i++) {
									if (x[i] > 0) {
										// if(NewSubset.contains(points.get(i)))
										{
											if (pointsReduced.containsKey(points.get(i))) {
												double value = Math.max(x[i], pointsReduced.get(points.get(i)));
												pointsReduced.put(points.get(i), value);
											} else {
												pointsReduced.put(points.get(i), x[i]);
											}
											// pointsReduced.add(points.get(i));

											IloLinearNumExpr exprNew = cplex.linearNumExpr();
											exprNew.addTerm(1, var._array[i]);
											cplex.addLe(exprNew, 0, "IgnoredVar" + currItr);
											currItr++;
										}
									}
								}

								cplex.clearCuts();
								// cplex.solve();
							}
						}
					}
				}
				cplex.clearLazyConstraints();
				cplex.clearCallbacks();
				cplex.clearCuts();
				cplex.clearModel();
				cplex.deleteNames();
				cplex.endModel();
				cplex.end();
				cplex = null;
			} catch (Exception e) {
				System.out.println("Concert exception caught: " + e);
			}
		}

		p = p + r;
		Map<Integer, Double> sortedPoints = sortByValue(pointsReduced);

		List<Integer> result = new ArrayList<Integer>();
		// add the sorted reduced points to the output
		for (Map.Entry<Integer, Double> en : sortedPoints.entrySet()) {
			result.add(en.getKey());
		}

		return result;

	}

	// old algorithm - only return list for one min unsafe unseparable
	public List<Integer> ConvexHull_new() {
		// System.out.println("Entered Convex Hull");
		p = p - r;
		List<Integer> points = new ArrayList<Integer>();
		//// List<Integer> points = new ArrayList<Integer>(MaxSafe);
		List<Integer> SafeIDX = new ArrayList<Integer>();
		int NumberOfVertices = MaxSafe.size();
		// Why do we need zero
		// SafeIDX.add(0);
		for (int i : MaxSafe) {
			SafeIDX.add(i);
		}

		double[][] vertices = new double[p][NumberOfVertices];
		for (int i = 0; i < SafeIDX.size(); i++) {
			int[] x = States.get(SafeIDX.get(i));
			for (int j = 0; j < p; j++)
				vertices[j][i] = x[j];
		}
		long startTime = System.currentTimeMillis();
		lp1cnt += MaxSafe.size();
		try {

			cplex = new IloCplex();
			{
				cplex.setOut(null);
				IloObjective modelObj = cplex.addMaximize();
				IloRange[] rng = new IloRange[p + 1];
				for (int j = 0; j < p; j++)
					rng[j] = cplex.addRange(0, 0, "coverDim" + j);
				rng[p] = cplex.addRange(1, 1, "convex");
				IloNumVarArray var = new IloNumVarArray();
				for (int i = 0; i < NumberOfVertices; i++) {
					IloColumn column;
					column = cplex.column(modelObj, 1);

					for (int j = 0; j < p; j++)
						column = column.and(cplex.column(rng[j], vertices[j][i]));
					column = column.and(cplex.column(rng[p], 1));
					var.add(cplex.numVar(column, 0., 1, "h" + i));
				}
				// cplex.exportModel("convex"+Integer.toString(itr1)+".lp");

				int counter = 0;

				for (int MSstate : MaxSafe) {

					// If the maximal state is on the convex hull of the states before pruning
					// then, it is on the convex hull of the states after pruning.
					if (parentConvexHullStates != null && parentConvexHullStates.contains(MSstate)) {
						points.add(MSstate);
						continue;
					}
					// The index of the state that we are considering from the set of safe states
					int itr1 = SafeIDX.indexOf(MSstate);
					for (int j = 0; j < p; j++)
						rng[j].setBounds(vertices[j][itr1], vertices[j][itr1]);
					cplex.setLinearCoef(modelObj, var.getElement(itr1), 0);
					cplex.setParam(IloCplex.IntParam.RootAlg, IloCplex.Algorithm.Dual);
					if (cplex.solve()) {
						double objective = cplex.getObjValue();

						if (objective < eps) // On the boundary
							points.add(SafeIDX.get(itr1));
						else // Suppress
							var.getElement(itr1).setUB(0);
					}
					cplex.setLinearCoef(modelObj, var.getElement(itr1), 1);

				}
			}
			cplex.clearLazyConstraints();
			cplex.clearCallbacks();
			cplex.clearCuts();
			cplex.clearModel();
			cplex.deleteNames();
			cplex.endModel();
			cplex.end();
			cplex = null;

		} catch (Exception e) {
			System.out.println("Concert exception caught: " + e);
		}
		myConvexHullStates.addAll(points);
		// p = p + r;
		long endTime = System.currentTimeMillis();
		// System.out.println("Convex Hull time = "+(endTime-startTime));
		// return points;
		/////////////////////////////////////////////////////////////////////////////////////////////////////////////
		// Only return the convex hull states that are in the convex hull of the minimal
		// states
		/////////////////////////////////////////////////////////////////////////////////////////////////////////////

		HashMap<Integer, Double> pointsReduced = new HashMap<Integer, Double>();

		double MaxObjective = 1000000;

		NumberOfVertices = points.size();
		vertices = new double[p][NumberOfVertices];
		for (int i = 0; i < points.size(); i++) {
			int[] x = States.get(points.get(i));
			for (int j = 0; j < p; j++)
				vertices[j][i] = x[j];
		}

		// for(int MinState : MinBoundaryUnsafeUnseparable)
		{
			Object[] temp = MinBoundaryUnsafeUnseparable.toArray();
			int MinState = (int) temp[0];
			for (int i = 1; i < temp.length; i++)
				if (((int) temp[i]) < MinState)
					MinState = (int) temp[i];
			try {
				cplex = new IloCplex();
				{
					cplex.setOut(null);
					cplex.setParam(IloCplex.DoubleParam.TiLim, 60);
					cplex.setWarning(null);
					IloObjective modelObj = cplex.addMaximize();
					IloRange[] rng = new IloRange[p + 1];

					for (int j = 0; j < p; j++)
						rng[j] = cplex.addRange(States.get(MinState)[j], Double.MAX_VALUE, "coverDim" + j);
					rng[p] = cplex.addRange(0, 1, "convex");
					IloNumVarArray var = new IloNumVarArray();
					for (int i = 0; i < NumberOfVertices; i++) {
						IloColumn column = cplex.column(modelObj, 1);

						for (int j = 0; j < p; j++)
							column = column.and(cplex.column(rng[j], vertices[j][i]));

						column = column.and(cplex.column(rng[p], 1));

						var.add(cplex.numVar(column, 0., 1, "h" + i));
					}

					int currItr = 0;
					boolean change = true;
					while (change) {
						change = false;
						lp2cnt++;

						if (cplex.solve()) {
							double objective = cplex.getObjValue();

							if (objective > eps)// the min unsafe is a combination of max unsafe
							{
								change = true;

								double[] x = new double[NumberOfVertices];
								for (int i = 0; i < NumberOfVertices; i++) {
									IloNumVar elem = var.getElement(i);
									x[i] = cplex.getValue(elem);
								}

								// HashSet<Integer> SafeSubset = new HashSet<Integer>();
								// for (int i = 0; i < NumberOfVertices; i++)
								// {
								// if(x[i] > 0)
								// {
								// SafeSubset.add(points.get(i));
								// }
								// }
								// HashSet<Integer> NewSubset = RemoveLinearSeparable(points, SafeSubset,
								// MinState);

								for (int i = 0; i < NumberOfVertices; i++) {
									if (x[i] > 0) {
										// if(NewSubset.contains(points.get(i)))
										{
											if (pointsReduced.containsKey(points.get(i))) {
												double value = Math.max(x[i], pointsReduced.get(points.get(i)));
												pointsReduced.put(points.get(i), value);
											} else {
												pointsReduced.put(points.get(i), x[i]);
											}
											// pointsReduced.add(points.get(i));

											IloLinearNumExpr exprNew = cplex.linearNumExpr();
											exprNew.addTerm(1, var._array[i]);
											cplex.addLe(exprNew, 0, "IgnoredVar" + currItr);
											currItr++;
										}
									}
								}

								cplex.clearCuts();
								// cplex.solve();
							}
						}
					}
				}
				cplex.clearLazyConstraints();
				cplex.clearCallbacks();
				cplex.clearCuts();
				cplex.clearModel();
				cplex.deleteNames();
				cplex.endModel();
				cplex.end();
				cplex = null;
			} catch (Exception e) {
				System.out.println("Concert exception caught: " + e);
			}
		}

		p = p + r;
		Map<Integer, Double> sortedPoints = sortByValue(pointsReduced);

		List<Integer> result = new ArrayList<Integer>();
		// add the sorted reduced points to the output
		for (Map.Entry<Integer, Double> en : sortedPoints.entrySet()) {
			result.add(en.getKey());
		}

		return result;

	}

	// old algorithm - only return list for one min unsafe unseparable
	// && work on max safe instead of extreme points of convex hull
	public List<Integer> ConvexHull_new_2() {
		// System.out.println("Entered Convex Hull");
		p = p - r;
		List<Integer> points = new ArrayList<Integer>(MaxSafe);
		int NumberOfVertices = MaxSafe.size();

		double[][] vertices = new double[p][NumberOfVertices];

		HashMap<Integer, Double> pointsReduced = new HashMap<Integer, Double>();

		double M = 1000;
		double MaxObjective = 1000000;

		NumberOfVertices = points.size();
		vertices = new double[p][NumberOfVertices];
		for (int i = 0; i < points.size(); i++) {
			int[] x = States.get(points.get(i));
			for (int j = 0; j < p; j++)
				vertices[j][i] = x[j];
		}

		{
			Object[] temp = MinBoundaryUnsafeUnseparable.toArray();
			int MinState = (int) temp[0];
			for (int i = 1; i < temp.length; i++)
				if (((int) temp[i]) < MinState)
					MinState = (int) temp[i];
			try {
				cplex = new IloCplex();
				{
					cplex.setOut(null);
					cplex.setParam(IloCplex.DoubleParam.TiLim, 60);
					cplex.setWarning(null);
					IloObjective modelObj = cplex.addMaximize();
					IloRange[] rng = new IloRange[p + 1];

					for (int j = 0; j < p; j++)
						rng[j] = cplex.addRange(States.get(MinState)[j], Double.MAX_VALUE, "coverDim" + j);
					rng[p] = cplex.addRange(0, 1, "convex");
					IloNumVarArray var = new IloNumVarArray();
					for (int i = 0; i < NumberOfVertices; i++) {
						IloColumn column = cplex.column(modelObj, 1);

						for (int j = 0; j < p; j++)
							column = column.and(cplex.column(rng[j], vertices[j][i]));

						column = column.and(cplex.column(rng[p], 1));

						var.add(cplex.numVar(column, 0., 1, "h" + i));
					}

					int currItr = 0;
					boolean change = true;
					while (change) {
						change = false;
						lp2cnt++;

						if (cplex.solve()) {
							double objective = cplex.getObjValue();

							if (objective > eps)// the min unsafe is a combination of max unsafe
							{
								change = true;

								double[] x = new double[NumberOfVertices];
								for (int i = 0; i < NumberOfVertices; i++) {
									IloNumVar elem = var.getElement(i);
									x[i] = cplex.getValue(elem);
								}

								for (int i = 0; i < NumberOfVertices; i++) {
									if (x[i] > 0) {
										{
											if (pointsReduced.containsKey(points.get(i))) {
												double value = Math.max(x[i], pointsReduced.get(points.get(i)));
												pointsReduced.put(points.get(i), value);
											} else {
												pointsReduced.put(points.get(i), x[i]);
											}
											// pointsReduced.add(points.get(i));

											IloLinearNumExpr exprNew = cplex.linearNumExpr();
											exprNew.addTerm(1, var._array[i]);
											cplex.addLe(exprNew, 0, "IgnoredVar" + currItr);
											currItr++;
										}
									}
								}

								cplex.clearCuts();
							}
						}
					}
				}
				cplex.clearLazyConstraints();
				cplex.clearCallbacks();
				cplex.clearCuts();
				cplex.clearModel();
				cplex.deleteNames();
				cplex.endModel();
				cplex.end();
				cplex = null;
			} catch (Exception e) {
				System.out.println("Concert exception caught: " + e);
			}
		}

		p = p + r;
		Map<Integer, Double> sortedPoints = sortByValue(pointsReduced);

		List<Integer> result = new ArrayList<Integer>();
		// add the sorted reduced points to the output
		for (Map.Entry<Integer, Double> en : sortedPoints.entrySet()) {
			result.add(en.getKey());
		}

		return result;

	}

	// Ahmed MIP - using Is as real variable not integer
	public List<Integer> ConvexHull_new_3() {
		// System.out.println("Entered Convex Hull");
		p = p - r;

		List<Integer> points = new ArrayList<Integer>(MaxSafe);
		HashMap<Integer, Double> pointsReduced = new HashMap<Integer, Double>();

		double M = 1000;

		try {
			cplex = new IloCplex();
			{
				cplex.setParam(IloCplex.IntParam.AdvInd, 0);

				cplex.setOut(null);
				IloObjective modelObj = cplex.addMaximize();
				IloRange[] rng = new IloRange[MaxSafe.size()];

				for (int i = 0; i < MaxSafe.size(); i++)
					rng[i] = cplex.addRange(Double.MAX_VALUE * -1, 0, "Safe" + i);
				IloNumVarArray var = new IloNumVarArray();
				// Hyerplane coefficients
				for (int j = 0; j < p; j++) {
					IloColumn column = cplex.column(modelObj, 0);
					int itr = 0;
					for (int i = 0; i < points.size(); i++) {
						int MSsafe = points.get(i);
						int[] x = States.get(MSsafe);
						if (x[j] != 0)
							column = column.and(cplex.column(rng[itr], x[j]));
						itr++;
					}
					var.add(cplex.numVar(column, 0., 1, "a" + j));
				}
				// Intercept
				IloColumn columnB = cplex.column(modelObj, 0);
				for (int i = 0; i < MaxSafe.size(); i++)
					columnB = columnB.and(cplex.column(rng[i], -1));
				var.add(cplex.numVar(columnB, 0., 1, "b"));
				// Is variables
				for (int j = 0; j < points.size(); j++) {
					IloColumn column = cplex.column(modelObj, -1);
					column = column.and(cplex.column(rng[j], -M));
					var.add(cplex.numVar(column, 0., 1, "a" + j));
				}

				Object[] temp = MinBoundaryUnsafeUnseparable.toArray();
				int MinUnsafe = (int) temp[0];
				for (int i = 1; i < temp.length; i++)
					if (((int) temp[i]) < MinUnsafe)
						MinUnsafe = (int) temp[i];

				IloLinearNumExpr exprNew = cplex.linearNumExpr();

				int[] MinUnsafeUn = States.get(MinUnsafe);
				// int[] x = States.get(MinUnsafe);
				for (int j = 0; j < p; j++)
					if (MinUnsafeUn[j] != 0)
						exprNew.addTerm(MinUnsafeUn[j], var._array[j]);

				exprNew.addTerm(-1, var._array[p]);

				IloRange myConstraint = cplex.addGe(exprNew, eps, "UnsafeState");
				if (cplex.solve()) {
					int abc = 0;

					double[] x = new double[p + MaxSafe.size() + 1];
					for (int i = 0; i < p + MaxSafe.size() + 1; i++) {
						IloNumVar elem = var.getElement(i);
						x[i] = cplex.getValue(elem);
					}

					for (int i = 0; i < points.size(); i++) {
						if (x[p + 1 + i] > 0) {
							double dist = 0;
							int[] MaxS = States.get(points.get(i));
							for (int j = 0; j < p; j++)
								dist += -(MaxS[j] - MinUnsafeUn[j]) * (MaxS[j] - MinUnsafeUn[j]);
							pointsReduced.put(points.get(i), dist);
						}
					}
				} else {
					System.out.println("Problem in the MIP");
				}
			}

			cplex.clearLazyConstraints();
			cplex.clearCallbacks();
			cplex.clearCuts();
			cplex.clearModel();
			cplex.deleteNames();
			cplex.endModel();
			cplex.end();
			cplex = null;
		} catch (Exception e) {
			System.out.println("Concert exception caught: " + e);
		}

		p = p + r;
		Map<Integer, Double> sortedPoints = sortByValue(pointsReduced);

		List<Integer> result = new ArrayList<Integer>();
		// add the sorted reduced points to the output
		for (Map.Entry<Integer, Double> en : sortedPoints.entrySet()) {
			result.add(en.getKey());
		}

		return result;

	}

	public List<Integer> ConvexHull_new_3_1() {

		// System.out.println("Entered Convex Hull");
		p = p - r;

		List<Integer> points = new ArrayList<Integer>(MaxSafe);
		HashMap<Integer, Double> pointsReduced = new HashMap<Integer, Double>();

		double M = 1000;

		try {
			
			{
				
				update_model_safe_states(matrix2,true);

				Object[] temp = MinBoundaryUnsafeUnseparable.toArray();
				int MinUnsafe = (int) temp[0];
				for (int i = 1; i < temp.length; i++)
					if (((int) temp[i]) < MinUnsafe)
						MinUnsafe = (int) temp[i];

				int[] MinUnsafeUn = States.get(MinUnsafe);
				update_model_unsafe_state(MinUnsafe, matrix2);
				
				if (cplex2.solve()) {
					double[] x     = cplex2.getValues(matrix2);
					for (int i = 0; i < points.size(); i++) {
						if (x[p + 1 + i] > 0) {
							double dist = 0;
							int[] MaxS = States.get(points.get(i));
							for (int j = 0; j < p; j++)
								dist += -(MaxS[j] - MinUnsafeUn[j]) * (MaxS[j] - MinUnsafeUn[j]);
							pointsReduced.put(points.get(i), dist);
						}
					}
					
				} else {
					System.out.println("Problem in the Convex Hull MIP");
				}
				cplex2.clearLazyConstraints();
				cplex2.clearCallbacks();
				cplex2.clearCuts();
			}

		} catch (Exception e) {
			System.out.println("Concert exception caught: " + e);
		}

		p = p + r;
		Map<Integer, Double> sortedPoints = sortByValue(pointsReduced);

		List<Integer> result = new ArrayList<Integer>();
		// add the sorted reduced points to the output
		for (Map.Entry<Integer, Double> en : sortedPoints.entrySet()) {
			result.add(en.getKey());
		}

		return result;

	}

	public void ReadPN(String file) {
		lp1cnt = 0;
		lp2cnt = 0;
		try {
			BufferedReader reader = new BufferedReader(new FileReader(file));
			p = Integer.parseInt(reader.readLine());
			t = Integer.parseInt(reader.readLine());
			r = Integer.parseInt(reader.readLine());
			m0 = new int[p];
			C = new int[p][t];
			String[] tokens2 = reader.readLine().split("\t");
			for (int i = 0; i < p; i++)
				m0[i] = Integer.parseInt(tokens2[i]);
			for (int i = 0; i < p; i++) {
				String[] tokens = reader.readLine().split("\t");
				for (int j = 0; j < t; j++)
					C[i][j] = Integer.parseInt(tokens[j]);
			}
			reader.close();
		} catch (Exception e) {

		}
	}

	int convert_int_to_str(int val,char [] ret)
	{
		if (val ==0)
		{
			ret[0] = '0';
			return 1;
		}
		int numOfDigits = (int)Math.log10(val) + 1;
		for(int i=0;i< numOfDigits; i++, val/=10)
		{
			int tmp = val % 10;
			ret[numOfDigits-1-i] = (char)(tmp + '0');
		}
		//System.out.println("ret = "+ret);
		//System.out.println("val = "+val);
		//System.out.println("numOfDigits = "+numOfDigits);
		return numOfDigits;
	}
	String join(char sep, int[] arr, int arrLen) {
		//Reset
		for(int i=0;i< joinHelper_size;i++)
			joinHelper[i] = 0;
		for(int i=0;i<p;i++)
			for(int j=0;j<joinIntHelper_size;j++)
				joinIntHelper[i][j] = 0;
		int lastIdx = 0;
		for(int i=0;i< arrLen; i++)
		{
			int len = convert_int_to_str(arr[i],joinIntHelper[i]);
			for(int k=0;k<len;k++)
				joinHelper[lastIdx+k] = joinIntHelper[i][k];
			lastIdx += len;
			//System.out.println("lastIdx = "+lastIdx);
			if (i < arrLen-1)
				joinHelper[lastIdx++] = sep;
		}
		
		return new String(joinHelper,0,lastIdx);
		
		
		
	}

	/// <summary>
	/// uses the C matrix and the initial marking to calculate all the reachable
	/// states
	/// </summary>
	public void CalculateReachableStates() {
		int currentState = 0;
		StateDict.put(join(',', m0, p - r), 0);
		States.add(m0);
		int[] s = new int[p];
		int[] m = new int[p];
		while (currentState < States.size()) {
			// 0- Initialize the next states
			HashSet<Integer> next = new HashSet<Integer>();
			// 1- Get the state that you want to explore
			
			for (int i = 0; i < p; i++)
				s[i] = States.get(currentState)[i];

			for (int j = 0; j < t; j++) {
				boolean reachable = true;
				for (int i = 0; i < p; i++) {
					m[i] = s[i];
					m[i] += C[i][j];
					if (m[i] < 0)
					{
						reachable = false;
					}
				}
				if (reachable) {
					String key = join(',', m, p - r);
					if (!StateDict.containsKey(key)) {
						StateDict.put(key, States.size());
						States.add(m);
					}
					next.add(StateDict.get(key));
					m = new int[p];
				}
			}

			NextStates.add(next);

			// 5-
			currentState++;

		}
		return;

	}

	/// <summary>
	/// divide the reachable states to safe and unsafe
	/// </summary>
	public void CalculateReachableSafeStates() {
		int l_numSafe = 1;
		for (int i = 0; i < States.size(); i++)
			Safe.add(false);
		Safe.set(0, true);
		boolean change = true;
		while (change) {
			change = false;
			for (int i = 0; i < States.size(); i++) {
				if (!Safe.get(i)) // not known yet
				{
					for (int j : NextStates.get(i))
						if (Safe.get(j)) {
							change = true;
							Safe.set(i, true);
							l_numSafe++;
							break;
						}
				}
			}

		}

		for (int i = 0; i < States.size(); i++) {
			HashSet<Integer> temp = new HashSet<Integer>();
			PreviousStates.add(temp);
		}
		for (int i = 0; i < NextStates.size(); i++) {
			for (int j : NextStates.get(i)) {
				PreviousStates.get(j).add(i);
			}
		}
		System.out.println("Total = " + States.size() + ", Number of safe " + l_numSafe + " , number of unsafe = "
				+ (States.size() - l_numSafe));

		

		return;
	}

	public void populateMaxMin(int stateIdx, int[] tokens2, int dir, HashSet<Integer> nonMaxMinStates) {
		int[] tokens1 = States.get(stateIdx);
		tokens2 = Arrays.copyOf(tokens1, p - r);
		for (int k = 0; k < p - r; k++) {

			if (tokens2[k] == 0 && dir == -1)
				continue;

			if (dir == -1)
				tokens2[k]--;
			else
				tokens2[k]++;
			String tokens2Str = this.join(',', tokens2, p - r);

			if (StateDict.containsKey(tokens2Str)) {
				int searchStateIdx = StateDict.get(tokens2Str);
				if (dir == -1) {
					nonMaxMinStates.add(searchStateIdx);
					addDominatedInfo(stateIdx, searchStateIdx);
				} else if (dir == 1)
					nonMaxMinStates.add(searchStateIdx);
			}
			if (dir == -1)
				tokens2[k]++;
			else
				tokens2[k]--;

		}
	}

	private void addDominatedInfo(int stateIdx, int searchStateIdx) {
		HashSet<Integer> dominatingSet;
		if (dominatedBy.containsKey(searchStateIdx)) {
			dominatingSet = dominatedBy.get(searchStateIdx);
		} else {
			dominatingSet = new HashSet<Integer>();
			dominatedBy.put(searchStateIdx, dominatingSet);
		}
		dominatingSet.add(stateIdx);

	}

	/// <summary>
	/// calculate the maximal safe and the minimal unsafe states
	/// </summary>
	public void CalculateMaxSafe() {
		long startTime = System.currentTimeMillis();

		MinBoundaryUnsafe = new HashSet<Integer>();
		for (int i = 0; i < States.size(); i++) {
			if (!Safe.get(i)) {
				boolean nonBoundary = true;
				for (int j : PreviousStates.get(i)) {
					if (Safe.get(j)) {
						MinBoundaryUnsafe.add(i);
						nonBoundary = false;
						break;

					}
				}
				if (nonBoundary)
					nonBoundayUnsafe.add(i);
			}
		}
		System.out.println("Passed 1");
		// Added New
		HashSet<Integer> nonMaximalSafe = new HashSet<Integer>();
		HashSet<Integer> nonMinimalBoundaryUnsafe = new HashSet<Integer>();
		int[] tokens2 = new int[p - r];
		for (int i = 0; i < States.size(); i++) {
			if (Safe.get(i)) {
				MaxSafe.add(i);
				populateMaxMin(i, tokens2, -1, nonMaximalSafe);
			} else if (MinBoundaryUnsafe.contains(i)) {
				populateMaxMin(i, tokens2, 1, nonMinimalBoundaryUnsafe);
			}
		}
		MinBoundaryUnsafe.removeAll(nonMinimalBoundaryUnsafe);
		MaxSafe.removeAll(nonMaximalSafe);

		// End Added New
		System.out.println("Passed 3");
		long endTime = System.currentTimeMillis();
		System.out.println("RAS first one time = " + (endTime - startTime));

	}

	/*
	 * A min boundary might become non-boundary -- reanalyze boundary A min boundary
	 * might be become dominated by any of the newly added unsafe states
	 * 
	 * A maximal safe states that remains safe is still maximal
	 * 
	 */
	public void CalculateMaxSafe(RAS parent) {
		long startTime = System.currentTimeMillis();
		// Init boundary unsafe
		MinBoundaryUnsafe = new HashSet<Integer>(parent.MinBoundaryUnsafe);
		HashSet<Integer> nonMinimalBoundaryUnsafe = new HashSet<Integer>();
		for (int i : MinBoundaryUnsafe) {
			Boolean isBoundary = false;
			for (int j : PreviousStates.get(i)) {
				if (Safe.get(j)) {
					isBoundary = true;
					break;
				}
			}
			if (!isBoundary)
				nonMinimalBoundaryUnsafe.add(i);
		}
		// Add new unsafe as candidates
		for (int i = 0; i < States.size(); i++) {
			if (parent.Safe.get(i) && !Safe.get(i)) {
				for (int j : PreviousStates.get(i)) {
					if (Safe.get(j)) {
						MinBoundaryUnsafe.add(i);
						break;
					}
				}
			}

		}
		// Extract the min ones
		int[] tokens2 = new int[p - r];

		for (int i : MinBoundaryUnsafe) {
			populateMaxMin(i, tokens2, 1, nonMinimalBoundaryUnsafe);

		}
		MinBoundaryUnsafe.removeAll(nonMinimalBoundaryUnsafe);

		// Review the maximal safe states
		for (int i = 0; i < States.size(); i++) {
			if (Safe.get(i)) {
				if (parent.MaxSafe.contains(i))
					MaxSafe.add(i);
				else // Previously non-maximal
				{
					HashSet<Integer> dominatingSet = dominatedBy.get(i);
					boolean isMax = true;
					for (int j : dominatingSet) {
						if (Safe.get(j)) {
							isMax = false;
							break;
						}
					}
					if (isMax)
						MaxSafe.add(i);
				}
			}
		}
		long endTime = System.currentTimeMillis();
		// System.out.println("RAS from parent time = "+(endTime-startTime));
		// System.out.println("Max Safe = "+MaxSafe.size()+" , Min unsafe =
		// "+MinBoundaryUnsafe.size());
		return;
	}

	public void UpdateMaxSafe(List<Boolean> ParentSafe) {
		long startTime = System.currentTimeMillis();
		// Init boundary unsafe
		// MinBoundaryUnsafe = new HashSet<Integer>(parent.MinBoundaryUnsafe);
		HashSet<Integer> ParentMaxSafe = new HashSet<Integer>(MaxSafe);
		MaxSafe.clear();
		HashSet<Integer> nonMinimalBoundaryUnsafe = new HashSet<Integer>();
		for (int i : MinBoundaryUnsafe) {
			Boolean isBoundary = false;
			for (int j : PreviousStates.get(i)) {
				if (Safe.get(j)) {
					isBoundary = true;
					break;
				}
			}
			if (!isBoundary)
				nonMinimalBoundaryUnsafe.add(i);
		}
		// Add new unsafe as candidates
		for (int i = 0; i < States.size(); i++) {
			if (ParentSafe.get(i) && !Safe.get(i)) {
				for (int j : PreviousStates.get(i)) {
					if (Safe.get(j)) {
						MinBoundaryUnsafe.add(i);
						break;
					}
				}
			}

		}
		// Extract the min ones
		int[] tokens2 = new int[p - r];

		for (int i : MinBoundaryUnsafe) {
			populateMaxMin(i, tokens2, 1, nonMinimalBoundaryUnsafe);

		}
		MinBoundaryUnsafe.removeAll(nonMinimalBoundaryUnsafe);

		// Review the maximal safe states
		for (int i = 0; i < States.size(); i++) {
			if (Safe.get(i)) {
				if (ParentMaxSafe.contains(i))
					MaxSafe.add(i);
				else // Previously non-maximal
				{
					HashSet<Integer> dominatingSet = dominatedBy.get(i);
					boolean isMax = true;
					for (int j : dominatingSet) {
						if (Safe.get(j)) {
							isMax = false;
							break;
						}
					}
					if (isMax)
						MaxSafe.add(i);
				}
			}
		}
		long endTime = System.currentTimeMillis();
		// System.out.println("RAS from parent time = "+(endTime-startTime));
		// System.out.println("Max Safe = "+MaxSafe.size()+" , Min unsafe =
		// "+MinBoundaryUnsafe.size());
		return;
	}

	public void CalculateMaxSafe1(RAS parent) {
		MinBoundaryUnsafe = new HashSet<Integer>(parent.MinBoundaryUnsafe);
		HashSet<Integer> Changed = new HashSet<Integer>();
		for (int i = 0; i < States.size(); i++)
			if (parent.Safe.get(i) && !Safe.get(i))
				Changed.add(i);

		for (int i : Changed) {
			for (int j : PreviousStates.get(i)) {
				if (Safe.get(j)) {
					MinBoundaryUnsafe.add(i);
					break;
				}
			}

		}
		//
		Object[] array = MinBoundaryUnsafe.toArray();
		for (int itr = array.length - 1; itr >= 0; itr--) {
			boolean remove = false;
			int[] tokens1 = States.get((int) array[itr]);

			for (int j = 0; j < array.length; j++) {
				if (j == itr)
					continue;
				boolean AllGreaterOrEqual = true;
				int[] tokens2 = States.get((int) array[j]);
				for (int k = 0; k < p - r; k++) {
					if (tokens1[k] < tokens2[k]) {
						AllGreaterOrEqual = false;
						break;
					}
				}
				if (AllGreaterOrEqual) {
					remove = true;
					break;
				}
			}
			if (remove) {
				MinBoundaryUnsafe.remove((int) array[itr]);
			}
		}

		//
		Changed.clear();
		MaxSafe = new HashSet<Integer>();
		for (int ParentMaxSafe : parent.MaxSafe)
			if (Safe.get(ParentMaxSafe))
				MaxSafe.add(ParentMaxSafe);

		for (int i = 0; i < States.size(); i++) {
			if (MaxSafe.contains(i))
				continue;
			if (Safe.get(i)) {
				boolean remove = false;
				int[] tokens1 = States.get(i);

				for (int j : MaxSafe) {
					boolean AllLessOrEqual = true;
					int[] tokens2 = States.get(j);
					for (int k = 0; k < p - r; k++) {
						if (tokens1[k] > tokens2[k]) {
							AllLessOrEqual = false;
							break;
						}
					}
					if (AllLessOrEqual) {
						remove = true;
						break;
					}
				}
				if (!remove) {
					MaxSafe.add(i);
				}
			}
		}

		Object[] arr = MaxSafe.toArray();
		for (int itr = arr.length - 1; itr >= 0; itr--) {
			boolean remove = false;
			int[] tokens1 = States.get((int) arr[itr]);

			for (int j = 0; j < arr.length; j++) {
				if (j == itr)
					continue;
				boolean AllLessOrEqual = true;
				int[] tokens2 = States.get((int) arr[j]);
				for (int k = 0; k < p - r; k++) {
					if (tokens1[k] > tokens2[k]) {
						AllLessOrEqual = false;
						break;
					}
				}
				if (AllLessOrEqual) {
					remove = true;
					break;
				}
			}
			if (remove) {
				MaxSafe.remove((int) arr[itr]);
			}
		}

	}

	void reviewSafety(int prunedState) {

		Queue<Integer> myQ = new LinkedList<>();
		HashSet<Integer> visited = new HashSet<Integer>();
		myQ.add(prunedState);
		visited.add(prunedState);
		while (!myQ.isEmpty()) {
			int stateIdx = myQ.poll();
			Safe.set(stateIdx, false);
			HashSet<Integer> l_prev = PreviousStates.get(stateIdx);
			for (int prevState : l_prev) {
				if (visited.contains(prevState))
					continue;
				visited.add(prevState);
				HashSet<Integer> nextToPrev = NextStates.get(prevState);
				boolean isSafe = false;
				for (int next : nextToPrev) {
					if (Safe.get(next)) {
						isSafe = true;
						break;
					}
				}
				if (!isSafe)
					myQ.add(prevState);

			}
		}

	}

	/// <summary>
	/// mark one of the states to be unsafe and modify the data accordingly
	/// </summary>
	/// <param name="state"></param>
	public void applyPruning() {
		if (parentRAS == null)
			return;
		long startTime = System.currentTimeMillis();
		reviewSafety(prunedState);
		/*
		 * // lines 1-4 of the algorithm //The set S will contains all the states s such
		 * that //s <= s'' for s'' \in \bar{S} (the maximal of the parent) except the
		 * pruned state Safe.set(PrunedState, false); HashSet<Integer> Shat_r = new
		 * HashSet<Integer>(); for(int i = 0; i < Safe.size() ;i++) if(Safe.get(i))
		 * Shat_r.add(i); Stack<Integer> Explore = new Stack<Integer>();
		 * HashSet<Integer> Tested = new HashSet<Integer>();
		 * 
		 * // line 5-7 of the algorithm HashSet<Integer> Shat_rs = new
		 * HashSet<Integer>(); Tested.clear(); Explore.add(0); while(Explore.size() > 0)
		 * { int current = Explore.pop(); for(int topush :
		 * RAS.PreviousStates.get(current)) { if(Shat_r.contains(topush)) {
		 * if(!Tested.contains(topush)) { Shat_rs.add(topush); Explore.add(topush);
		 * Tested.add(topush); } }
		 * 
		 * } }
		 * 
		 * for(int i = 0; i < Safe.size(); i++) Safe.set(i, false); for(int i : Shat_rs)
		 * Safe.set(i, true);
		 */
		long time1 = System.currentTimeMillis();
		// line 8 of the algorithm
		CalculateMaxSafe(parentRAS);
		/*
		 * System.out.println("Number of reachable safe states before pruning "+Shat_r.
		 * size());
		 * System.out.println("Number of reachable safe states after pruning "+Shat_rs.
		 * size()); System.out.println("Number of maximal safe states "+MaxSafe.size());
		 * System.out.println("Number of minimal unsafe states "+MinBoundaryUnsafe.size(
		 * )); printStates2();
		 */
		// This calculates the number of safe states
		CalculateSafeCount();
		long time2 = System.currentTimeMillis();

	}

	public List<List<Double>> LinearPlans() {
		List<List<Double>> Plans = new ArrayList<List<Double>>();

		p = p - r;

		MinBoundaryUnsafeUnseparable.clear();
		try {
			cplex = new IloCplex();
			{
				cplex.setParam(IloCplex.IntParam.AdvInd, 0);

				cplex.setOut(null);
				IloObjective modelObj = cplex.addMaximize();
				IloRange[] rng = new IloRange[MaxSafe.size()];

				for (int i = 0; i < MaxSafe.size(); i++)
					rng[i] = cplex.addRange(Double.MAX_VALUE * -1, 0, "Safe" + i);
				IloNumVarArray var = new IloNumVarArray();
				// Hyerplane coefficients
				for (int j = 0; j < p; j++) {
					IloColumn column = cplex.column(modelObj, 0);
					int itr = 0;
					for (int MSsafe : MaxSafe) {
						int[] x = States.get(MSsafe);
						if (x[j] != 0)
							column = column.and(cplex.column(rng[itr], x[j]));
						itr++;
					}
					var.add(cplex.numVar(column, 0., 1, "a" + j));
				}
				// Intercept
				IloColumn columnB = cplex.column(modelObj, 0);
				for (int i = 0; i < MaxSafe.size(); i++)
					columnB = columnB.and(cplex.column(rng[i], -1));
				var.add(cplex.numVar(columnB, 0., 1, "b"));

				for (int MinUnsafe : MinBoundaryUnsafe) {
					int[] x = States.get(MinUnsafe);
					boolean covered = false;
					for (int i = 0; i < Plans.size(); i++) {
						double total = 0;
						for (int j = 0; j < p; j++)
							total += x[j] * Plans.get(i).get(j);
						total -= Plans.get(i).get(p);
						if (total > 0) {
							covered = true;
							break;
						}
					}
					if (covered)
						continue;

					IloLinearNumExpr exprNew = cplex.linearNumExpr();
					for (int j = 0; j < p; j++)
						if (x[j] != 0)
							exprNew.addTerm(x[j], var._array[j]);

					exprNew.addTerm(-1, var._array[p]);

					IloRange myConstraint = cplex.addGe(exprNew, eps, "UnsafeState");

					if (cplex.solve()) {
						Double[] sol = new Double[p + 1];
						for (int i = 0; i < p + 1; i++) {
							IloNumVar elem = var.getElement(i);
							sol[i] = cplex.getValue(elem) / eps;
						}
						List<Double> Plan = new ArrayList<Double>();
						for (int i = 0; i < p + 1; i++)
							Plan.add((double) sol[i]);
						Plans.add(Plan);
					}
					cplex.delete(myConstraint);
					cplex.clearCuts();

				}

				for (int itr = 0; itr < States.size(); itr++) {
					if (!Safe.get(itr)) {
						int[] x = States.get(itr);
						boolean covered = false;
						for (int i = 0; i < Plans.size(); i++) {
							double total = 0;
							for (int j = 0; j < p; j++)
								total += x[j] * Plans.get(i).get(j);
							total -= Plans.get(i).get(p);
							if (total > 0) {
								covered = true;
								break;
							}
						}
						if (covered)
							continue;

						IloLinearNumExpr exprNew = cplex.linearNumExpr();
						for (int j = 0; j < p; j++)
							if (x[j] != 0)
								exprNew.addTerm(x[j], var._array[j]);

						exprNew.addTerm(-1, var._array[p]);

						IloRange myConstraint = cplex.addGe(exprNew, eps, "UnsafeState");

						if (cplex.solve()) {
							Double[] sol = new Double[p + 1];
							for (int i = 0; i < p + 1; i++) {
								IloNumVar elem = var.getElement(i);
								sol[i] = cplex.getValue(elem) / eps;
							}
							List<Double> Plan = new ArrayList<Double>();
							for (int i = 0; i < p + 1; i++)
								Plan.add((double) sol[i]);
							Plans.add(Plan);
						}
						cplex.delete(myConstraint);
						cplex.clearCuts();
					}
				}

			}
			cplex.clearLazyConstraints();
			cplex.clearCallbacks();
			cplex.clearCuts();
			cplex.clearModel();
			cplex.deleteNames();
			cplex.endModel();
			cplex.end();
			cplex = null;
		} catch (Exception e) {
			System.out.println("Concert exception caught: " + e);
		}
		p = p + r;
		return Plans;
	}

	public void update_model_safe_states(IloLPMatrix p_matrix,boolean add_indicator) {
		try {
			double M = 1000;
			int num_max_safe = MaxSafe.size();
			int max_num_constraints;
			if (add_indicator)
				max_num_constraints = max_num_constraints2;
			else
				max_num_constraints = max_num_constraints3;
			
			if (num_max_safe > max_num_constraints) {
				// Add more empty constraints
				int diff = num_max_safe - max_num_constraints;
				double[] lhs = new double[diff];
				double[] rhs = new double[diff];
				int added_cols = p+1;
				if (add_indicator)
					added_cols = p+2;
					
				double[][] val = new double[diff][added_cols];
				int[][] ind = new int[diff][added_cols];
				for (int i = 0; i < diff; i++) {
					lhs[i] = -Double.MAX_VALUE;
					rhs[0] = 0;
					for (int j = 0; j < p; j++) {
						val[i][j] = 0.0;
						ind[i][j] = j;
					}
					val[i][p] = -1.0;
					ind[i][p] = p;
					if(add_indicator)
					{
						val[i][p+1] = -M;
						ind[i][p+1] = p+1+i+max_num_constraints;
					}
				}
				if (add_indicator)
					max_num_constraints2 = num_max_safe;
				else
					max_num_constraints3 = num_max_safe;
				
				p_matrix.addRows(lhs, rhs, ind, val);
				
			} else if (num_max_safe < max_num_constraints) {// Disable additional constraints
				int diff = max_num_constraints - MaxSafe.size();
				int[] row_idx = new int[diff * p];
				int[] col_idx = new int[diff * p];
				double[] val = new double[diff * p];
				for (int i = 0; i < diff; i++) {
					for (int j = 0; j < p; j++) {
						row_idx[j + i * p] = i + num_max_safe + 1;// additional 1 to account for the unsafe state
																	// constraint
						col_idx[j + i * p] = j;
						val[j + i * p] = 0.0;
					}
				}
				
				p_matrix.setNZs(row_idx, col_idx, val);
				
			}

			int[] safe_row_idx = new int[num_max_safe * p];
			int[] safe_col_idx = new int[num_max_safe * p];
			double[] safe_val = new double[num_max_safe * p];
			int row_idx = 0;
			for (int MSsafe : MaxSafe) {
				int[] x = States.get(MSsafe);
				for (int j = 0; j < p; j++) {
					safe_row_idx[row_idx * p + j] = row_idx + 1; // additional 1 to account for the unsafe state
																	// constraint
					safe_col_idx[row_idx * p + j] = j;
					safe_val[row_idx * p + j] = x[j];

				}
				row_idx++;
			}
			
			p_matrix.setNZs(safe_row_idx, safe_col_idx, safe_val);
			
		} catch (Exception e) {
			System.out.println("Concert exception caught: " + e);
		}

	}
	public void update_model_unsafe_state(int MinUnsafe,IloLPMatrix p_matrix)
	{
		try
		{
			int[] x = States.get(MinUnsafe);
			for (int j = 0; j < p; j++) {
				unsafe_row_idx[j] = 0;
				unsafe_col_idx[j] = j;
				unsafe_val[j] = x[j];
	
			}
			p_matrix.setNZs(unsafe_row_idx, unsafe_col_idx, unsafe_val);
		}
		catch (Exception e) {
			System.out.println("Concert exception caught: " + e);
		}
	}
	public boolean LinearSpearable() {
		return LinearSpearable(-1);
	}

	public boolean LinearSpearable(int target_min_unsafe) {
		p = p - r;

		MinBoundaryUnsafeUnseparable.clear();
		try {
			update_model_safe_states(matrix3,false);
			HashSet<Integer> targetSet;
			if (target_min_unsafe == -1)
				targetSet = MinBoundaryUnsafe;
			else {
				targetSet = new HashSet<Integer>();
				targetSet.add(target_min_unsafe);
			}
			for (int MinUnsafe : targetSet) {
				update_model_unsafe_state(MinUnsafe,matrix3);
				if (cplex3.solve()) {
					int abc = 0;
				} else {
					MinBoundaryUnsafeUnseparable.add(MinUnsafe);
				}
				cplex3.clearLazyConstraints();
				cplex3.clearCallbacks();
				cplex3.clearCuts();

			}
			
			
		} catch (Exception e) {
			System.out.println("Failed to solve LinearSpearable");
		}
		p = p + r;
		
		if (MinBoundaryUnsafeUnseparable.size() == 0)
			return true;

		return false;
	}

	/*
	 * public boolean LinearSpearable(int MinUnsafe) { boolean sep = true; p = p -
	 * r; double eps = 0.0001; try { IloRange [] rng3 = new
	 * IloRange[MaxSafe.size()];
	 * 
	 * IloLinearNumExpr[] SafeExpr = new IloLinearNumExpr[MaxSafe.size()]; int itr =
	 * 0; for (int MSsafe : MaxSafe) { SafeExpr[itr] = cplex3.linearNumExpr(); int[]
	 * x = States.get(MSsafe); for(int j = 0; j < p; j++) if(x[j] != 0)
	 * SafeExpr[itr].addTerm(x[j], var3._array[j]); SafeExpr[itr].addTerm(-1,
	 * var3._array[p]); rng3[itr] = cplex3.addLe(SafeExpr[itr], 0, "State"+itr);
	 * itr++; }
	 * 
	 * { IloLinearNumExpr exprNew = cplex3.linearNumExpr();
	 * 
	 * int[] x = States.get(MinUnsafe); for(int j = 0; j < p; j++) if(x[j] != 0)
	 * exprNew.addTerm(x[j], var3._array[j]);
	 * 
	 * exprNew.addTerm(-1, var3._array[p]);
	 * 
	 * IloRange myConstraint = cplex3.addGe(exprNew, eps, "UnsafeState");
	 * if(cplex3.solve()) { sep = true; } else { sep = false; }
	 * cplex3.delete(myConstraint); cplex3.clearCuts();
	 * 
	 * } for(int i = 0; i < MaxSafe.size(); i++) { cplex3.delete(rng3[i]); }
	 * 
	 * //cplex3.end(); //cplex3 = null;
	 * 
	 * } catch (Exception e) { System.out.println("Concert exception caught: " + e);
	 * } p = p + r;
	 * 
	 * return sep; }
	 * 
	 * public boolean LinearSpearable2(int MinUnsafe) { boolean sep = true; p = p -
	 * r; double eps = 0.0001; try { IloCplex cplex = new IloCplex();
	 * cplex.setParam(IloCplex.IntParam.AdvInd, 0);
	 * 
	 * cplex.setOut(null); IloObjective modelObj = cplex.addMaximize(); IloRange []
	 * rng = new IloRange[MaxSafe.size()];
	 * 
	 * for (int i = 0; i < MaxSafe.size(); i++) rng[i] =
	 * cplex.addRange(Double.MAX_VALUE*-1,0, "Safe"+i); IloNumVarArray var = new
	 * IloNumVarArray(); //Hyerplane coefficients for(int j=0;j<p;j++) { IloColumn
	 * column = cplex.column(modelObj, 0); int itr = 0; for (int MSsafe : MaxSafe) {
	 * int[] x = States.get(MSsafe); if(x[j] != 0) column =
	 * column.and(cplex.column(rng[itr], x[j])); itr++; }
	 * var.add(cplex.numVar(column, 0., 1 ,"a"+j)); } //Intercept IloColumn columnB
	 * = cplex.column(modelObj, 0); for (int i = 0; i < MaxSafe.size(); i++) columnB
	 * = columnB.and(cplex.column(rng[i], -1)); var.add(cplex.numVar(columnB, 0., 1
	 * ,"b"));
	 * 
	 * 
	 * { IloLinearNumExpr exprNew = cplex.linearNumExpr();
	 * 
	 * int[] x = States.get(MinUnsafe); for(int j = 0; j < p; j++) if(x[j] != 0)
	 * exprNew.addTerm(x[j], var._array[j]);
	 * 
	 * exprNew.addTerm(-1, var._array[p]);
	 * 
	 * IloRange myConstraint = cplex.addGe(exprNew, eps, "UnsafeState");
	 * if(cplex.solve()) { sep = true; } else { sep = false; }
	 * cplex.delete(myConstraint); cplex.clearCuts();
	 * 
	 * }
	 * 
	 * 
	 * cplex.end(); cplex = null;
	 * 
	 * } catch (Exception e) { System.out.println("Concert exception caught: " + e);
	 * } p = p + r;
	 * 
	 * return sep; }
	 */

	/// <summary>
	/// check whether the maximal safe and minimal unsafe are linearly separable or
	/// not.
	/// </summary>
	/// <returns></returns>
	public boolean LinearSpearable2() {
		p = p - r;
		// Ahmed -- M can be set to p * max val in states
		double M = 1000;
		// Solve the MIP from the file
		try {
			cplex = new IloCplex();
			{
				cplex.setOut(null);
				IloObjective modelObj = cplex.addMaximize();
				IloRange[][] rng = new IloRange[2][];
				rng[0] = new IloRange[MaxSafe.size()];
				rng[1] = new IloRange[MinBoundaryUnsafe.size()];
				for (int i = 0; i < MaxSafe.size(); i++)
					rng[0][i] = cplex.addRange(Double.MAX_VALUE * -1, 0, "Safe" + i);
				for (int i = 0; i < MinBoundaryUnsafe.size(); i++)
					rng[1][i] = cplex.addRange(eps - M, Double.MAX_VALUE, "Unsafe" + i);
				IloNumVarArray var = new IloNumVarArray();
				// Hyerplane coefficients
				for (int j = 0; j < p; j++) {
					IloColumn column = cplex.column(modelObj, 0);
					int itr = 0;
					for (int MSsafe : MaxSafe) {
						int[] x = States.get(MSsafe);
						if (x[j] != 0)
							column = column.and(cplex.column(rng[0][itr], x[j]));
						itr++;
					}
					itr = 0;
					for (int MinUnsafe : MinBoundaryUnsafe) {
						int[] x = States.get(MinUnsafe);
						if (x[j] != 0)
							column = column.and(cplex.column(rng[1][itr], x[j]));
						itr++;
					}
					var.add(cplex.numVar(column, 0., 1, "a" + j));
				}
				// Intercept
				IloColumn columnB = cplex.column(modelObj, 0);
				for (int i = 0; i < MaxSafe.size(); i++)
					columnB = columnB.and(cplex.column(rng[0][i], -1));
				for (int i = 0; i < MinBoundaryUnsafe.size(); i++)
					columnB = columnB.and(cplex.column(rng[1][i], -1));
				var.add(cplex.numVar(columnB, 0., 1, "b"));
				// Indicators for separation
				for (int i = 0; i < MinBoundaryUnsafe.size(); i++) {
					IloColumn column = cplex.column(modelObj, 1);
					column = column.and(cplex.column(rng[1][i], -M));
					var.add(cplex.boolVar(column, "d" + i));
				}

				int TotalSeparated = 0;
				boolean change = true;
				List<Integer> SeparatedCoeff = new ArrayList<Integer>();
				for (int i = 0; i < MinBoundaryUnsafe.size(); i++)
					SeparatedCoeff.add(1);

				int numIter = 0;
				while (change) {
					change = false;
					IloLinearNumExpr obj = cplex.linearNumExpr();
					for (int k = 0; k < p + 1; k++)
						obj.addTerm(0, var._array[k]);
					for (int k = 0; k < SeparatedCoeff.size(); k++) {
						obj.addTerm(SeparatedCoeff.get(k), var._array[p + 1 + k]);
						// cplex.setLinearCoef(modelObj, 0, arg2);

					}
					modelObj.setExpr(obj);
					// IloLinearNumExpr obj2 = (IloLinearNumExpr) modelObj.getExpr();
					cplex.objective(modelObj.getSense());

					// modelObj = cplex.addMaximize(obj);
					// cplex.setLinearCoef(modelObj, obj);
					// cplex.exportModel("Linear"+numIter+".lp");
					cplex.solve();

					double[] x = new double[p + 1];
					for (int i = 0; i < p + 1; i++) {
						IloNumVar elem = var.getElement(i);
						x[i] = cplex.getValue(elem);
					}
					for (int i = p + 1; i < p + 1 + MinBoundaryUnsafe.size(); i++) {
						IloNumVar elem = var.getElement(i);
						double d = cplex.getValue(elem);
						if ((SeparatedCoeff.get(i - p - 1) == 1) && (d > 0.99)) {
							TotalSeparated++;
							SeparatedCoeff.set(i - p - 1, 0);
							change = true;
						}
					}
					if (TotalSeparated == MinBoundaryUnsafe.size()) {
						cplex.clearLazyConstraints();
						cplex.clearCallbacks();
						cplex.clearCuts();
						cplex.clearModel();
						cplex.deleteNames();
						cplex.endModel();
						cplex.end();
						cplex = null;
						p = p + r;
						return true;
					}

					numIter++;
				}
			}
			cplex.clearLazyConstraints();
			cplex.clearCallbacks();
			cplex.clearCuts();
			cplex.clearModel();
			cplex.deleteNames();
			cplex.endModel();
			cplex.end();
			cplex = null;

		} catch (Exception e) {
			System.out.println("Concert exception caught: " + e);
		}
		p = p + r;
		return false;
	}

	public RAS() {

		init_cplex();
	}
	public void init_cplex()
	{
		try
		{
			cplex = new IloCplex();
			cplex2 = new IloCplex();
			cplex3 = new IloCplex();
			matrix3 = cplex3.addLPMatrix();
			matrix2 = cplex2.addLPMatrix();
			cplex3.setParam(IloCplex.IntParam.AdvInd, 0);
			cplex3.setOut(null);
			double[] lb3 = new double[p - r + 1];
			double[] ub3 = new double[p - r + 1];
			for (int j = 0; j < p - r + 1; j++) {
				lb3[j] = 0;
				ub3[j] = 1.0;
			}
			cplex3.numVarArray(cplex3.columnArray(matrix3, p - r + 1), lb3, ub3);
			
			double[] lhs = { eps };
			double[] rhs = { Double.MAX_VALUE };
			double[][] val = new double[1][p - r + 1];
			int[][] ind = new int[1][p - r + 1];
			for (int j = 0; j < p - r +1; j++) {
				val[0][j] = 0.0;
				ind[0][j] = j;
			}
			val[0][p-r] = -1;
			
			matrix3.addRows(lhs, rhs, ind, val);
			///////////////////////////////////////////////////////////////
			cplex2.setOut(null);
			cplex2.setParam(IloCplex.IntParam.AdvInd, 0);
			double[] lb2 = new double[p - r + 1+Safe.size()];
			double[] ub2 = new double[p - r + 1+Safe.size()];
			double [] obj2 =  new double[p - r + 1+Safe.size()];
			for (int j = 0; j <p - r + 1+Safe.size(); j++) {
				lb2[j] = 0;
				ub2[j] = 1.0;
				if (j<p - r + 1)
					obj2[j] = 0.0;
				else
					obj2[j] = -1.0;
			}
			IloNumVar[] x_var2 = cplex2.numVarArray(cplex2.columnArray(matrix2, p - r + 1+Safe.size()), lb2, ub2);
			matrix2.addRows(lhs, rhs, ind, val);
			cplex2.add(cplex2.maximize(cplex2.scalProd(obj2,x_var2)));
			
			unsafe_row_idx = new int [p-r];
			unsafe_col_idx =new int [p-r];
			unsafe_val = new double [p-r];
			max_num_constraints3 = 0;
			max_num_constraints2 = 0;
			
		}
		catch (Exception e) {
			System.out.println("Concert exception caught: " + e);
		}
	}
		
	public RAS(String pn) {
		
		ReadPN(pn);
		joinHelper_size = p*2*10;
		joinIntHelper_size = 10;
		joinHelper = new char[joinHelper_size];
		joinIntHelper = new char[p][joinIntHelper_size];
		//
		CalculateReachableStates();
		CalculateReachableSafeStates();
		// RemoveNonboundaryUnsafeStates();
		CalculateMaxSafe();
		// ConvexHull();
		CalculateSafeCount();
		System.out.println("Number of reachable safe states " + this.safeCount);
		System.out.println("Number of maximal safe states " + MaxSafe.size());
		System.out.println("Number of minimal unsafe states " + MinBoundaryUnsafe.size());
		System.out.println("Dim = " + (p - r));

		ReduceMemory_NonBoundaryUnsafe();
		init_cplex();
		return;
		// printStates();
	}

	// This function reduces memory usage by eliminating unnecessary data from
	// Non-Boundary unsafe states
	void ReduceMemory_NonBoundaryUnsafe() {
		for (int i = 0; i < States.size(); i++) {
			if (!Safe.get(i)) {
				boolean allunsafe = true;
				for (int j : PreviousStates.get(i)) {
					if (Safe.get(j)) {
						allunsafe = false;
						break;
					}
				}
				// This is an unsafe non-boundary state
				if (allunsafe) {
					PreviousStates.get(i).clear();
					NextStates.get(i).clear();
					if (!StateDict.remove(join(',', States.get(i), p - r), i))
						System.out.println("Problem");

				}
			}
		}
	}

	void printStates() {
		System.out.println("All States");
		System.out.println("*************");
		for (int i = 0; i < States.size(); i++) {
			int[] x = States.get(i);
			System.out.print(i + " : ");
			for (int j = 0; j < p - r; j++)
				System.out.print(x[j] + ",");
			System.out.print(" || ");
			if (this.Safe.get(i))
				System.out.print(" Safe ");
			else
				System.out.print(" Unsafe ");
			System.out.print(" || ");
			if (this.MaxSafe.contains(i))
				System.out.print(" Max Safe ");
			if (this.MinBoundaryUnsafe.contains(i))
				System.out.print(" Min Unsafe ");

			System.out.println("");
		}
		System.out.println("Reachability");
		System.out.println("*************");
		for (int i = 0; i < States.size(); i++) {
			System.out.print(i + "-->");
			for (int j : NextStates.get(i))
				System.out.print(j + ",");
			System.out.println("");
		}
		System.out.println("");
	}

	void printStates2() {
		System.out.println("Maximal safe");
		System.out.println("*************");
		for (int i = 0; i < States.size(); i++) {
			if (!this.MaxSafe.contains(i))
				continue;
			int[] x = States.get(i);
			System.out.print(i + " : ");
			for (int j = 0; j < p - r; j++)
				System.out.print(x[j] + ",");
			System.out.println("");
		}

		System.out.println("Minimal unsafe");
		System.out.println("*************");
		for (int i = 0; i < States.size(); i++) {
			if (!this.MinBoundaryUnsafe.contains(i))
				continue;
			int[] x = States.get(i);
			System.out.print(i + " : ");
			for (int j = 0; j < p - r; j++)
				System.out.print(x[j] + ",");
			System.out.println("");
		}

	}

	void printMaxSafe() {
		System.out.println("Maximal safe");
		System.out.println("*************");
		for (int i = 0; i < States.size(); i++) {
			if (!this.MaxSafe.contains(i))
				continue;
			int[] x = States.get(i);
			System.out.print(i + " : ");
			for (int j = 0; j < p - r; j++)
				System.out.print(x[j] + ",");
			System.out.println("");
		}
	}

	/// <summary>
	/// copy constructor for deep copying
	/// </summary>
	/// <param name="ras"></param>
	public RAS(RAS parentRAS, int prunedState) {
		this.parentRAS = parentRAS;
		m0 = null;
		C = null;
		this.prunedState = prunedState;
		// StateDict.clear();

		Safe = new ArrayList<Boolean>(parentRAS.Safe);
		MaxSafe = new HashSet<Integer>();// ras.MaxSafe
		MinBoundaryUnsafe = new HashSet<Integer>();// ras.MinUnsafe
		parentConvexHullStates = parentRAS.myConvexHullStates;
		init_cplex();

	}

	@Override
	public int compareTo(RAS arg0) {
		return Integer.compare(arg0.safeCount, this.safeCount);
	}

}