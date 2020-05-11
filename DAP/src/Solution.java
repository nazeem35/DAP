/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/**
 *
 * @author mayke
 */
public class Solution
{
    //static Algorithm a = new Algorithm("C:\\Users\\mayke\\Desktop\\");
    //static Algorithm a = new Algorithm("/Users/ahmednazeem/git/DAP/");
    
    public static void main(String[] args)
    {
    	long startTime = System.currentTimeMillis();
    	Algorithm a = new Algorithm("C:\\Users\\mayke\\Desktop\\Unseparable\\");
    	//a.SolvePN();
    	a.SolvePN_fast_new();
    	long endTime = System.currentTimeMillis();
    	System.out.println("Stack time = "+(endTime-startTime));
        /*if (args[0].equals( "solve"))
        {
            a.SolvePN();
        }
        else if (args[0].equals( "solve_max"))
        {
        	a.SolvePNMax();
        }
        else if (args[0].equals("write_results"))
        {
            a.WriteResults();
        }
        else
        {
            System.out.println("Invalid command, possible commands: solve, solve_max and write_results");
        }*/
    }
}

