/**
 * RV class declaration
 *
 * @author: Fedor Shmarov
 * @e-mail: f.shmarov@ncl.ac.uk
 */
 
#ifndef RV_H  
#define RV_H  

#include<string>
#include<sstream>

using namespace std;

class RV
{ 
	private:
		string name;
		string var;
		string fun;
		double left;
		double right;
	public:
		RV(string, string, string, double, double);
		string getName();
		string getVar();
		string getFun();
		double getLeft();
		double getRight();
		string toString();
}; 
#endif  