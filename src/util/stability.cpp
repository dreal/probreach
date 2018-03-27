//
// Created by fedor on 21/03/18.
//

#include "stability.h"
#include "pdrh.h"
#include <cmath>
#include <algorithm>
#include <engine.h>
#include <cstring>

#define  BUFSIZE 256

using namespace std;

bool stability::jury_test(std::vector<double> poly)
{
    // getting the size of the polynomials
    size_t n = poly.size()-1;

    // condition 1
    if(abs(poly.back()) >= poly.front()) return false;

    // condition 2
    double res = 0;
    for(double value : poly)
    {
        res += value;
    }
    if(res <= 0) return false;

    // condition 3
    // n is even
    if(n % 2 == 0)
    {
        res = 0;
        double sign = 1;
        for(double value : poly)
        {
            res += sign*value;
            sign = -sign;
        }
        if(res <= 0) return false;
    }
    // n is odd
    else
    {
        res = 0;
        double sign = -1;
        for(double value : poly)
        {
            res += sign*value;
            sign = -sign;
        }
        if(res >= 0) return false;
    }

    // condition 4
    // reversing the table
    for(size_t j = 0; j < n - 2; j++)
    {
        size_t m = poly.size() - 1;
        vector<double> new_row;
        for(size_t i = 0; i < m; i++)
        {
            new_row.push_back(poly.at(m)*poly.at(i+1) - poly.at(0)*poly.at(m-1-i));
        }
        //reverse(new_row.begin(), new_row.end());
        if(abs(new_row.back()) <= abs(new_row.front())) return false;
        //reverse(new_row.begin(), new_row.end());
        poly = new_row;
    }

    return true;
}

std::vector<double> stability::get_char_poly(std::map<std::string, pdrh::node *> odes, double Tt, box init, vector<box> boxes)
{
    // creating capd string here
    // declaring parameters
//    string par_string = "par:";
//    for(box b : boxes)
//    {
//        map<string, capd::interval> b_map = b.get_map();
//        for(auto it = b_map.begin(); it != b_map.end(); it++)
//        {
//            par_string += it->first + ',';
//        }
////        cout << b << endl;
//    }
//    par_string.back() = ';';

    vector<string> vars;

    // declaring variables
    string var_string = "var:";
    string fun_string = "fun:";
    int odes_size = 0;
    for(auto it = odes.begin(); it != odes.end(); it++)
    {
        if(it->first == "u")
        {
            vars.push_back(it->first);
            var_string += it->first + ',';
            fun_string += pdrh::node_to_string_infix(it->second) + ',';
            odes_size++;
        }
        else
        {
            if((pdrh::node_to_string_infix(it->second) != "0") &&
                (pdrh::node_to_string_infix(it->second) != "1"))
            {
                vars.push_back(it->first);
                var_string += it->first + ',';
                fun_string += pdrh::node_to_string_infix(it->second) + ',';
                odes_size++;
            }
        }
    }
    var_string.back() = ';';
    fun_string.back() = ';';

//    cout << par_string << endl;
//    cout << var_string << endl;
//    cout << fun_string << endl;

    // creating an ODE solver and setting precision
    //capd::DMap odes_rhs(par_string + var_string + fun_string);
    capd::DMap odes_rhs(var_string + fun_string);

    //setting parameter values
//    for(box b : boxes)
//    {
//        map<string, capd::interval> b_map = b.get_map();
//        for(auto it = b_map.begin(); it != b_map.end(); it++)
//        {
//            odes_rhs.setParameter(it->first, it->second.rightBound());
//        }
//    }

    cout << "Init: " << init << endl;

    // setting initial condition here
    capd::DVector init_vector(odes_size), res_vector(odes_size);
    map<string, capd::interval> init_map = init.get_map();
    size_t i = 0;
    for(auto it = init_map.begin(); it != init_map.end(); it++)
    {
        init_vector[i] = it->second.rightBound();
        i++;
    }

    cout << "Obtaining a big matrix: " << endl;
    capd::DMatrix Df = odes_rhs.derivative(init_vector);
    cout << Df << endl;

    for(string var : vars)
    {
        cout << var << endl;
    }


    // deriving matrices A and B from the big matrix

    size_t i_index = 0;
    size_t j_index = 0;

    capd::DMatrix A(Df.numberOfRows()-1, Df.numberOfColumns()-1);
    capd::DMatrix B(Df.numberOfRows()-1, 1);

    for(size_t i = 0; i < A.numberOfRows(); i++)
    {
        if(vars.at(i) == "u") i_index = 1;
        for(size_t j = 0; j < A.numberOfColumns(); j++)
        {
            if(vars.at(j) == "u")
            {
                B[i][0] = Df[i][j];
                j_index = 1;
            }
            A[i][j] = Df[i+i_index][j+j_index];
        }
        j_index = 0;
    }

    cout << "Matrix A:" << endl;
    cout << A << endl;

    cout << "Matrix B:" << endl;
    cout << B << endl;

//    cout << "Matrix A*T:" << endl;
//    cout << A*T << endl;
//
//    arma::mat matA(A.numberOfRows(), A.numberOfColumns());
//    arma::mat matB(B.numberOfRows(), 1);
//
//    for(size_t i = 0; i < A.numberOfRows(); i++)
//    {
//        for(size_t j = 0; j < A.numberOfColumns(); j++)
//        {
//            matA(i,j) = A[i][j];
//        }
//        matB(i,0) = B[i][0];
//    }
//
//    cout << "Matrix A*T arma:" << endl;
//    cout << matA*T << endl;
//
//    arma::mat matG = arma::expmat(matA*T);
//    cout << "Matrix G:" << endl;
//    cout << matG << endl;
//
//    cout << "Matrix B arma:" << endl;
//    cout << matB << endl;
//
//    // computing integral integral
//    arma::mat matH(B.numberOfRows(), 1);
//    size_t n = 1000;
//    for(size_t i = 0; i < n; i++)
//    {
//        matH += arma::expmat(matA*(T*i/n))*matB*(T/n);
//    }
//    cout << "Matrix H arma:" << endl;
//    cout << matH << endl;
//
//    arma::mat matC(1, A.numberOfColumns());
//    matC(0, A.numberOfColumns()-1) = 1;
//    cout << "Matrix C arma:" << endl;
//    cout << matC << endl;
//
//    arma::mat matD(1,1);
//    matD(0,0) = 0;
//
//    arma::mat matI = arma::eye<arma::mat>(A.numberOfRows(), A.numberOfColumns());
//    arma::mat matSS2TF = matC*arma::inv(matI-matG)*matH+matD;
//    cout << "SS2TF:" << endl;
//    cout << matSS2TF << endl;

    Engine *ep;
    mxArray *T = NULL, *result = NULL;
    char buffer[BUFSIZE+1];
    double time[10] = { 0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0 };

    /*
     * Call engOpen with a NULL string. This starts a MATLAB process
     * on the current host using the command "matlab".
     */
    if (!(ep = engOpen(""))) {
        fprintf(stderr, "\nCan't start MATLAB engine\n");
        exit(EXIT_FAILURE);
    }

    /*
     * PART I
     *
     * For the first half of this demonstration, we will send data
     * to MATLAB, analyze the data, and plot the result.
     */

    /*
     * Create a variable for our data
     */
    T = mxCreateDoubleMatrix(1, 10, mxREAL);
    memcpy((void *)mxGetPr(T), (void *)time, sizeof(time));
    /*
     * Place the variable T into the MATLAB workspace
     */
    engPutVariable(ep, "T", T);

    /*
     * Evaluate a function of time, distance = (1/2)g.*t.^2
     * (g is the acceleration due to gravity)
     */
    engEvalString(ep, "D = .5.*(-9.8).*T.^2;");

    /*
     * Plot the result
     */
    engEvalString(ep, "plot(T,D);");
    engEvalString(ep, "title('Position vs. Time for a falling object');");
    engEvalString(ep, "xlabel('Time (seconds)');");
    engEvalString(ep, "ylabel('Position (meters)');");

    /*
     * use fgetc() to make sure that we pause long enough to be
     * able to see the plot
     */
    printf("Hit return to continue\n\n");
    fgetc(stdin);
    /*
     * We're done for Part I! Free memory, close MATLAB figure.
     */
    printf("Done for Part I.\n");
    mxDestroyArray(T);
    engEvalString(ep, "close;");


    /*
     * PART II
     *
     * For the second half of this demonstration, we will request
     * a MATLAB string, which should define a variable X.  MATLAB
     * will evaluate the string and create the variable.  We
     * will then recover the variable, and determine its type.
     */

    /*
     * Use engOutputBuffer to capture MATLAB output, so we can
     * echo it back.  Ensure first that the buffer is always NULL
     * terminated.
     */

    buffer[BUFSIZE] = '\0';
    engOutputBuffer(ep, buffer, BUFSIZE);
    while (result == NULL) {
        char str[BUFSIZE+1];
        char *input = NULL;
        /*
         * Get a string input from the user
         */
        printf("Enter a MATLAB command to evaluate.  This command should\n");
        printf("create a variable X.  This program will then determine\n");
        printf("what kind of variable you created.\n");
        printf("For example: X = 1:5\n");
        printf(">> ");

        input = fgets(str, BUFSIZE, stdin);

        /*
         * Evaluate input with engEvalString
         */
        engEvalString(ep, str);

        /*
         * Echo the output from the command.
         */
        printf("%s", buffer);

        /*
         * Get result of computation
         */
        printf("\nRetrieving X...\n");
        if ((result = engGetVariable(ep,"X")) == NULL)
            printf("Oops! You didn't create a variable X.\n\n");
        else {
            printf("X is class %s\t\n", mxGetClassName(result));
        }
    }

    /*
     * We're done! Free memory, close MATLAB engine and exit.
     */
    printf("Done!\n");
    mxDestroyArray(result);
    engClose(ep);


}









