


class Solution
{
    //String path = @"C:\Users\Michael\Desktop\Linear DAP\Unseparable\";
    static Algorithm a = new Algorithm("/Users/ahmednazeem/Documents/PT/");
    public static void main(String[] args)
    {
        if (args[0].equals( "solve"))
        {
            a.SolvePN();
        }
        else if (args[0].equals("write_results"))
        {
            a.WriteResults();
        }
        else
        {
            System.out.println("Invalid command, possible commands: generate, solve and write_results");

        }
    }
}




