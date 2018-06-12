


class Solution
{
    static Algorithm a = new Algorithm("C:\\Users\\Michael\\Desktop\\Linear DAP\\Unseparable\\");
    //static Algorithm a = new Algorithm("/Users/ahmednazeem/Documents/PT/");
    
    public static void main(String[] args)
    {
    	//a.SolvePNMax();
        if (args[0].equals( "solve"))
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
        }
    }
}




