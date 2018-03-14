//
// Created by kny on 27/02/18.
//

#include "engine.h"
#include "translator.h"
#include "../util/pdrh.h"

using namespace std;

void print_map(map<string, pair<pdrh::node*, pdrh::node*>>& map1){
    for (auto& t : map1)
        std::cout << t.first << " "
                  << t.second.first << " "
                  << t.second.second << "\n";
}

void translator::parse_tree(){
    cout<<pdrh::model_to_string();
    print_map(pdrh::var_map);
    print_map(pdrh::par_map);
    test_engine_call();
}

double translator::test_engine_call() {
    // Create arrays of Matlab type
    mxArray *X = mxCreateDoubleMatrix(1, 1, mxREAL);
    mxArray *Y = mxCreateDoubleMatrix(1, 1, mxREAL);

    // Matlab arrays --> double arrays
    double *ptrToMatX = reinterpret_cast<double *>(mxGetData(X));
    double *ptrToMatY = reinterpret_cast<double *>(mxGetData(Y));

    // Manipulate ordinary c++ arrays
    ptrToMatX[0] = 1;
    ptrToMatY[0] = 2;

    // Start the Matlab Engine
    engine *ep;
    if (!(ep = engOpen("\0"))) {
        fprintf(stderr, "\nCan't start MATLAB engine\n");
        return 0;
    }

    // Copy the variables into Matlab prompt
    engPutVariable(ep, "X", X);
    engPutVariable(ep, "Y", Y);

    // Call the function
    engEvalString(ep, "Z = (X + Y^2)");

    // Copy the variable from Matlab prompt to our code
    mxArray *Z = engGetVariable(ep, "Z");

    // Convert this variable to ordinary c++ array and show it
    double *ptrToMatZ = reinterpret_cast<double *>(mxGetData(Z));
    std::cout << "result is " << *ptrToMatZ << std::endl;

    return *ptrToMatZ;
}

