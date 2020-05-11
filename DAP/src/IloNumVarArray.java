import ilog.concert.IloNumVar;

public class IloNumVarArray {
	  int _num           = 0;
      IloNumVar[] _array = new IloNumVar[32];

      void add(IloNumVar ivar) {
         if ( _num >= _array.length ) {
            IloNumVar[] array = new IloNumVar[2 * _array.length];
            System.arraycopy(_array, 0, array, 0, _num);
            _array = array;
         }
         _array[_num++] = ivar;
      }

      IloNumVar getElement(int i) { return _array[i]; }
      int       getSize()         { return _num; }
      IloNumVar[] getArray() { return _array;}
      IloNumVar[] getEffArray()
      {
    	  IloNumVar[] ret = new IloNumVar[_num];
    	  System.arraycopy(_array, 0, ret, 0, _num);
    	  return ret;
      }
      IloNumVar[] getPartialArray(int from,int to)
      {
    	  IloNumVar[] ret = new IloNumVar[to-from];
    	  System.arraycopy(_array, from, ret, 0, to-from);
    	  return ret;
      }
}