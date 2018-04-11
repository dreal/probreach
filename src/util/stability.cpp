//
// Created by fedor on 21/03/18.
//

#include "stability.h"
#include "pdrh.h"
#include "pdrh_config.h"
#include <cmath>
#include <algorithm>
//#include <engine.h>
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


bool stability::is_stable(std::map<std::string, pdrh::node *> odes, double T, box init, box param)
{

    vector<string> vars;

    // declaring variables
    string var_string = "var:";
    string fun_string = "fun:";
    int odes_size = 0;
    for(auto it = odes.begin(); it != odes.end(); it++)
    {
        if(it->first[0] == 'u' && it->first[1] == '_')
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

//    cout << "Init: " << init << endl;

    // setting initial condition here
    capd::DVector init_vector(odes_size), res_vector(odes_size);
    map<string, capd::interval> init_map = init.get_map();
    size_t i = 0;
    size_t p = 0;
    size_t q = 0;
    for(auto it = init_map.begin(); it != init_map.end(); it++)
    {
        if(it->first[0] == 'e' && it->first[1] == '_')
        {
            p++;
        }
        if(it->first[0] == 'u' && it->first[1] == '_')
        {
            init_vector[i] = it->second.rightBound();
            q++;
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

    // there are three error terms
    p = p / 3;



//    cout << "Init vector: " << init_vector << endl;

//    capd::DVector coeff;
//    odes_rhs.computeODECoefficients(coeff, 1);

//    cout << "Map degree: " << odes_rhs.degree() << endl;
//    cout << "Map order: " << odes_rhs.getOrder() << endl;


//    cout << "Obtaining a big matrix: " << endl;
    capd::DMatrix Df = odes_rhs.derivative(init_vector);
//    cout << Df << endl;
//
//
//    for(string var : vars)
//    {
//        cout << var << endl;
//    }


    // deriving matrices A and B from the big matrix

    size_t i_index = 0;
    size_t j_index = 0;

    size_t n = Df.numberOfRows()-p;
    size_t m = Df.numberOfColumns()-p;

    // from here we are working with arrays of doubles
    double A[n][m];
    double B[n][p];
    double C[q][m];
    double D[q][1];

    for(size_t i = 0; i < n; i++)
    {
        for(size_t j = 0; j < m; j++)
        {
            A[i][j] = 0;
        }
    }

    for(size_t i = 0; i < n; i++)
    {
        for(size_t j = 0; j < p; j++)
        {
            B[i][j] = 0;
        }
    }

    for(size_t i = 0; i < q; i++)
    {
        for(size_t j = 0; j < m; j++)
        {
            C[i][j] = 0;
        }
    }

    for(size_t i = 0; i < q; i++)
    {
        D[i][0] = 0;
    }

    size_t i_end = 0;
    size_t j_end = 0;
    size_t i_out = 0;
    for(size_t i = 0; i < Df.numberOfRows(); i++)
    {
        if(vars.at(i)[0] != 'u')
        {
            j_end = 0;
            for(size_t j = 0; j < Df.numberOfColumns(); j++)
            {
                if(vars.at(j)[0] != 'u')
                {
                    A[j_end][i_end] = Df[i][j];
                    j_end++;
                }
            }
            i_end++;
        }
        if(vars.at(i) == "phi" || vars.at(i) == "psi" || vars.at(i) == "the")
        {
            j_end = 0;
            for(size_t j = 0; j < Df.numberOfColumns(); j++)
            {
                if(vars.at(j)[0] != 'u')
                {
                    C[i_out][j_end] = Df[i][j];
                    j_end++;
                }
            }
            i_out++;
        }
    }

    i_end = 0;
    j_end = 0;
    for(size_t i = 0; i < Df.numberOfRows(); i++)
    {
        if(vars.at(i)[0] != 'u')
        {
            j_end = 0;
            for(size_t j = 0; j < Df.numberOfColumns(); j++)
            {
                if(vars.at(j)[0] == 'u')
                {
                    B[i_end][j_end] = Df[i][j];
                    j_end++;
                }
            }
            i_end++;
        }
    }


//    cout << "Matrix A:" << endl;
//    for(size_t i = 0; i < n; i++)
//    {
//        for(size_t j = 0; j < m; j++)
//        {
//            cout << A[i][j] << " ";
//        }
//        cout << endl;
//    }
//
//    cout << "Matrix B:" << endl;
//    for(size_t i = 0; i < n; i++)
//    {
//        for(size_t j = 0; j < p; j++)
//        {
//            cout << B[i][j] << " ";
//        }
//        cout << endl;
//    }
//
//    cout << "Matrix C:" << endl;
//    for(size_t i = 0; i < q; i++)
//    {
//        for(size_t j = 0; j < n; j++)
//        {
//            cout << C[i][j] << " ";
//        }
//        cout << endl;
//    }
//
//    cout << "Matrix D:" << endl;
//    for(size_t i = 0; i < q; i++)
//    {
//        cout << D[i][0] << endl;
//    }

//    // initialising matlab engine
//    Engine *ep;
//    if (!(ep = engOpen(""))) {
//        fprintf(stderr, "\nCan't start MATLAB engine\n");
//        exit(EXIT_FAILURE);
//    }
//
//    // initialising matrices
//    mxArray *matA = NULL, *matB = NULL, *matC = NULL, *matD = NULL;
//
//    matA = mxCreateDoubleMatrix(n, m, mxREAL);
//    memcpy((void *)mxGetPr(matA), (void *)A, sizeof(A));
//    engPutVariable(ep, "A", matA);
//
//    matB = mxCreateDoubleMatrix(n, p, mxREAL);
//    memcpy((void *)mxGetPr(matB), (void *)B, sizeof(B));
//    engPutVariable(ep, "B", matB);
//
//    matC = mxCreateDoubleMatrix(q, m, mxREAL);
//    memcpy((void *)mxGetPr(matC), (void *)C, sizeof(C));
//    engPutVariable(ep, "C", matC);
//
//    matD = mxCreateDoubleMatrix(q, 1, mxREAL);
//    memcpy((void *)mxGetPr(matD), (void *)D, sizeof(D));
//    engPutVariable(ep, "D", matD);
//
//    //engEvalString(ep, "cd /home/b2049657/probreach-ap/src/matlab/");
//
//    engEvalString(ep, "cd /home/fedor/probreach-ap/src/matlab/");
//
//    stringstream ss;
//    ss << "check_stability(A,B,C,D," << T << "," << param.get_map()["Kp"].leftBound() << "," << param.get_map()["Ki"].leftBound() << "," << param.get_map()["Kd"].leftBound() << ");";
//    engEvalString(ep, ss.str().c_str());
//
////    cout << "MATLAB command: " << ss.str() << endl;
////
////    result = engGetVariable(ep, "A");
////    double *resA = mxGetPr(result);
////    cout << "Matrix A from matlab: " << endl;
////    for(size_t i = 0; i < m*n; i++)
////    {
////        cout << resA[i] << " ";
////    }
////    cout << endl;
////
////    result = engGetVariable(ep, "B");
////    double *resB = mxGetPr(result);
////    cout << "Matrix B from matlab: " << endl;
////    for(size_t i = 0; i < n; i++)
////    {
////        cout << resB[i] << " ";
////    }
////    cout << endl;
////
////    result = engGetVariable(ep, "C");
////    double *resC = mxGetPr(result);
////    cout << "Matrix C from matlab: " << endl;
////    for(size_t i = 0; i < m; i++)
////    {
////        cout << resC[i] << " ";
////    }
////    cout << endl;
//
////    for(size_t i = 0; i < n; i++)
////    {
////        cout << mxGetPr(result)[i] << endl;
////    }
//
//    double res = mxGetPr(engGetVariable(ep, "ans"))[0];
//
//    // freeing the memory
//    mxDestroyArray(matA);
//    mxDestroyArray(matB);
//    mxDestroyArray(matC);
//    mxDestroyArray(matD);
//    engClose(ep);
//
//    return res == 0;
}




