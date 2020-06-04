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
    
	static int  convert_int_to_str(int val,char [] ret)
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
		return numOfDigits;
	}
	
    public static void main(String[] args)
    {
    	long startTime = System.currentTimeMillis();
    	//Algorithm a = new Algorithm("C:\\Users\\mayke\\Desktop\\Unseparable\\");
    	Algorithm a = new Algorithm("/Users/ahmednazeem/git/DAP/");
    	//a.SolvePN();
    	//char [] tmp = new char[10];
    	//int n = convert_int_to_str(0,tmp);
    	
    	//System.out.println(String.valueOf(tmp));
    	//System.out.println(String.valueOf(n));
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

