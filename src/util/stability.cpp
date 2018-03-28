//
// Created by fedor on 21/03/18.
//

#include "stability.h"
#include "pdrh.h"
#include "pdrh_config.h"
#include <cmath>
#include <algorithm>
#include <engine.h>
#include <cstring>

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

std::vector<double> stability::get_char_poly(std::map<std::string, pdrh::node *> odes, double T, box init, vector<box> boxes)
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
    cout << var_string << endl;
    cout << fun_string << endl;

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
    capd::DVector init_vector(odes_size-1), res_vector(odes_size-1);
    map<string, capd::interval> init_map = init.get_map();
    size_t i = 0;
    for(auto it = init_map.begin(); it != init_map.end(); it++)
    {
        if(it->first == "u")
        {
            init_vector[i] = it->second.rightBound();
            i++;
        }
        else
        {
            // only those whose ODEs are not 0 or 1 will go in
            if((pdrh::node_to_string_infix(odes[it->first]) != "0") &&
               (pdrh::node_to_string_infix(odes[it->first]) != "1"))
            {
                init_vector[i] = it->second.rightBound();
                i++;
            }
        }
    }

    cout << "Init vector: " << init_vector << endl;

//    capd::DVector coeff;
//    odes_rhs.computeODECoefficients(coeff, 1);

    cout << "Map degree: " << odes_rhs.degree() << endl;
    cout << "Map order: " << odes_rhs.getOrder() << endl;


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

    int n = Df.numberOfRows()-1;
    int m = Df.numberOfColumns()-1;

    // from here we are working with arrays of doubles
    double A[n][m];
    double B[n][1];
    double C[1][m];
    double D[1][1];

    for(size_t i = 0; i < n; i++)
    {
        for(size_t j = 0; j < m; j++)
        {
            A[i][j] = 0;
        }
        B[i][0] = 0;
        C[0][i] = 0;
    }
    D[0][0] = 0;

    for(size_t i = 0; i < n; i++)
    {
        if(vars.at(i) == "u") i_index = 1;
        for(size_t j = 0; j < m; j++)
        {
            if(vars.at(j) == "u")
            {
                B[i][0] = Df[i][j];
                j_index = 1;
            }
            A[j][i] = Df[i+i_index][j+j_index];
        }
        if(vars.at(i) == "Q1")
        {
            C[0][i] = 1;
        }
        j_index = 0;
    }

    cout << "Matrix A:" << endl;
    for(size_t i = 0; i < n; i++)
    {
        for(size_t j = 0; j < m; j++)
        {
            cout << A[i][j] << " ";
        }
        cout << endl;
    }

    cout << "Matrix B:" << endl;
    for(size_t i = 0; i < n; i++)
    {
        cout << B[i][0] << endl;
    }

    cout << "Matrix C:" << endl;
    for(size_t i = 0; i < n; i++)
    {
        cout << C[0][i] << " ";
    }
    cout << endl;

    cout << "Matrix D:" << endl;
    cout << D[0][0] << endl;


    /*
     * Call engOpen with a NULL string. This starts a MATLAB process
     * on the current host using the command "matlab".
     */
    Engine *ep;
    if (!(ep = engOpen(""))) {
        fprintf(stderr, "\nCan't start MATLAB engine\n");
        exit(EXIT_FAILURE);
    }

    mxArray *matA = NULL, *matB = NULL, *matC = NULL, *matD = NULL, *result = NULL, *res = NULL;

    matA = mxCreateDoubleMatrix(n, m, mxREAL);
    memcpy((void *)mxGetPr(matA), (void *)A, sizeof(A));
    engPutVariable(ep, "A", matA);

    matB = mxCreateDoubleMatrix(n, 1, mxREAL);
    memcpy((void *)mxGetPr(matB), (void *)B, sizeof(B));
    engPutVariable(ep, "B", matB);

    matC = mxCreateDoubleMatrix(1, m, mxREAL);
    memcpy((void *)mxGetPr(matC), (void *)C, sizeof(C));
    engPutVariable(ep, "C", matC);

    matD = mxCreateDoubleMatrix(1, 1, mxREAL);
    memcpy((void *)mxGetPr(matD), (void *)D, sizeof(D));
    engPutVariable(ep, "D", matD);

    res = mxCreateDoubleMatrix(1, 1, mxREAL);
    memcpy((void *)mxGetPr(res), (void *)res, sizeof(res));
    engPutVariable(ep, "res", res);

    double Kp = -0.0009466876514559384;
    double Ki = -3.651948677736389e-04;
    double Kd = -0.0041651834714520;

    engEvalString(ep, "cd /home/fedor/probreach-ap/src/matlab/");

    stringstream ss;
    ss << "res = check_stability(A,B,C,D," << T << "," << Kp << "," << Ki << "," << Kd << ");";
    engEvalString(ep, ss.str().c_str());

    cout << "MATLAB command: " << ss.str() << endl;

    result = engGetVariable(ep, "A");
    double *resA = mxGetPr(result);
    cout << "Matrix A from matlab: " << endl;
    for(size_t i = 0; i < m*n; i++)
    {
        cout << resA[i] << " ";
    }
    cout << endl;

    result = engGetVariable(ep, "B");
    double *resB = mxGetPr(result);
    cout << "Matrix B from matlab: " << endl;
    for(size_t i = 0; i < n; i++)
    {
        cout << resB[i] << " ";
    }
    cout << endl;

    result = engGetVariable(ep, "C");
    double *resC = mxGetPr(result);
    cout << "Matrix C from matlab: " << endl;
    for(size_t i = 0; i < m; i++)
    {
        cout << resC[i] << " ";
    }
    cout << endl;



    // getting the matrix straight away
    result = engGetVariable(ep, "res");

    cout << "Result: " << mxGetPr(result)[0] << endl;
//    for(size_t i = 0; i < n; i++)
//    {
//        cout << mxGetPr(result)[i] << endl;
//    }

    mxDestroyArray(matA);
    mxDestroyArray(matB);
    mxDestroyArray(matC);
    mxDestroyArray(matD);
    mxDestroyArray(result);

//    engEvalString(ep, "close;");
    engClose(ep);


}









