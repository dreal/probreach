#include <stdio.h>
//#include <crtdbg.h>
//#include <Windows.h>
#include <memory>
#include <vector>

#include "GpDataset.h"
#include "AnalyticApproximation.h"
#include "SmmcOptions.h"
#include "SmoothedModelCheker.h"
#include "ProbitRegressionPosterior.h"
#include <iostream>
#include <cstring>
#include <sstream>
#include <fstream>
#include <logging/easylogging++.h>
#include <solver/dreal_wrapper.h>
#include "node.h"
#include "model.h"
#include "naive.h"
#include "git_sha1.h"
#include "version.h"
#include "box.h"
#include "pdrh2box.h"
#include "mc.h"
#include "pdrh_config.h"
//#include <gsl/gsl_blas.h>
//#include <gsl/gsl_multimin.h>
//#include <gsl/gsl_math.h>
//#include <gsl/gsl_ieee_utils.h>
#include <gsl/gsl_rng.h>
#include <gsl/gsl_qrng.h>
#include <gsl/gsl_cdf.h>
#include <capd/intervals/lib.h>
#include "pdrh2box.h"
//#include "algorithm.h"
#include "qmc.h"
#include "easylogging++.h"
#include "pdrh_config.h"
#include <chrono>
#include <iomanip>
#include "rnd.h"
//#include "stability.h"
#include <omp.h>

#include "DebugLogMatrix.h"

using namespace std;
std::ofstream myfile("test.csv");

extern "C"
{
#include "pdrhparser.h"
}

INITIALIZE_EASYLOGGINGPP

extern "C" int yyparse();
extern "C" FILE *yyin;

using namespace std;
using namespace pdrh;

// the minimum depth of each path
size_t min_depth = 0;
// the maximum depth of each path
size_t max_depth = 0;
// number of points
size_t num_points = 1;
// path to the input file
string in_file = "";
// minimisation flag
//bool minimise_flag = false;
// half-size of the computed confidence intervals
//double acc = 1e-1;
// confidence value for the computed confidence intervals
double conf = 0.95;
// number of iterations of cross-entropy algorithm
//size_t num_iter = 2;
// number of sample of each iteration of cross-entropy algorithm
size_t num_samples = 10;

// printing help message
void print_help() {
    cout << "Usage:" << endl;
    cout << endl;
    cout << "	simulate <options> <file.pdrh/file.drh> <solver-options>" << endl;
    cout << endl;
    cout << "options:" << endl;
    cout << "-h - displays help message" << endl;
    cout << "-v - prints out the current version of ProbReach" << endl;
    cout << "-l - minimum depth of every simulation path (default = " << min_depth << ")" << endl;
    cout << "-u - maximum depth of every simulation path (default = " << max_depth << ")" << endl;
    cout << "-n - number of points (default = " << num_points << ")" << endl;
    //cout << "--min - minimise reachability probability (default = " << minimise_flag << ")" << endl;
    //cout << "--acc - half-size of the computed confidence intervals (default = " << acc << ")" << endl;
    cout << "--conf - confidence value for the computed confidence intervals (default = " << conf << ")" << endl;
    //cout << "--iter - confidence value for the computed confidence intervals (default = " << num_iter << ")" << endl;
    cout << "--samples - number of samples for each iteration of cross-entropy algorithm (default = " << num_samples
         << ")" << endl;
    cout << "--solver - full path to the solver executable (default = " << dreal::solver_bin << ")" << endl;
}

// parsing command line options
void parse_cmd(int argc, char *argv[]) {
    //parsing ProbReach options
    for (int i = 1; i < argc; i++) {
        // filename
        if (string(argv[i]).substr(string(argv[i]).find_last_of('.') + 1) == "pdrh" ||
            string(argv[i]).substr(string(argv[i]).find_last_of('.') + 1) == "drh") {
            in_file = argv[i];
        }
            // help
        else if (string(argv[i]) == "-h") {
            print_help();
            exit(EXIT_SUCCESS);
        }
            // version
        else if (string(argv[i]) == "-v") {
            cout << "ProbReach " << PROBREACH_VERSION << " (" << git::get_sha1() << ")" << endl;
            exit(EXIT_SUCCESS);
        }
            // minimum path length
        else if (string(argv[i]) == "-l") {
            i++;
            istringstream is(argv[i]);
            is >> min_depth;
            if (min_depth < 0) {
                cerr << "-l must be positive and not larger than -u";
                exit(EXIT_FAILURE);
            }
        }
            // maximum path length
        else if (string(argv[i]) == "-u") {
            i++;
            istringstream is(argv[i]);
            is >> max_depth;
            if (max_depth < 0) {
                cerr << "-u must be positive and not smaller than -l";
                exit(EXIT_FAILURE);
            }
        }
            // maximum number of points
        else if (string(argv[i]) == "-n") {
            i++;
            istringstream is(argv[i]);
            is >> num_points;
            if (num_points < 0) {
                cerr << "-n must be positive";
                exit(EXIT_FAILURE);
            }
        }
            // confidence
        else if ((strcmp(argv[i], "--conf") == 0)) {
            i++;
            istringstream is(argv[i]);
            is >> conf;
            if (conf <= 0 || conf >= 1) {
                cerr << "--conf must be a number from (0,1) interval";
                exit(EXIT_FAILURE);
            }
        }
            // number of samples per iteration of cross-entropy algorithm
        else if ((strcmp(argv[i], "--samples") == 0)) {
            i++;
            istringstream is(argv[i]);
            is >> num_samples;
            if (num_samples <= 0) {
                cerr << "--samples must be positive";
                exit(EXIT_FAILURE);
            }
        } else if (string(argv[i]) == "--solver") {
            i++;
            dreal::solver_bin = string(argv[i]);
        }
    }
    // checking if the input file is specified
    if (in_file == "") {
        cerr << "Input file has not been specified" << endl;
        exit(EXIT_FAILURE);
    }
}




//void test() {
//	double beta = 2.0;
//	const int ncolumns = 1; // Dimention of nondet parameters (1 or 2)
//	double x_points[][ncolumns] = { {0.005},
//{0.005979899497487437},
//{0.006959798994974875},
//{0.007939698492462312},
//{0.00891959798994975},
//{0.009899497487437188},
//{0.010879396984924626},
//{0.011859296482412063},
//{0.012839195979899501},
//{0.013819095477386939},
//{0.014798994974874377},
//{0.015778894472361814},
//{0.01675879396984925},
//{0.017738693467336687},
//{0.018718592964824123},
//{0.01969849246231156},
//{0.020678391959798995},
//{0.02165829145728643},
//{0.022638190954773867},
//{0.023618090452261303},
//{0.02459798994974874},
//{0.025577889447236175},
//{0.02655778894472361},
//{0.027537688442211047},
//{0.028517587939698483},
//{0.02949748743718592},
//{0.030477386934673355},
//{0.031457286432160794},
//{0.032437185929648234},
//{0.03341708542713567},
//{0.03439698492462311},
//{0.03537688442211055},
//{0.03635678391959799},
//{0.03733668341708543},
//{0.03831658291457287},
//{0.03929648241206031},
//{0.04027638190954775},
//{0.04125628140703519},
//{0.04223618090452263},
//{0.04321608040201007},
//{0.04419597989949751},//40
//{0.04517587939698495},
//{0.046155778894472387},
//{0.047135678391959826},
//{0.048115577889447265},
//{0.049095477386934705},
//{0.050075376884422144},
//{0.051055276381909584},
//{0.05203517587939702},
//{0.05301507537688446},
//{0.0539949748743719},
//{0.05497487437185934},
//{0.05595477386934678},
//{0.05693467336683422},
//{0.05791457286432166},
//{0.0588944723618091},
//{0.05987437185929654},
//{0.06085427135678398},
//{0.06183417085427142},
//{0.06281407035175886},
//{0.06379396984924629},
//{0.06477386934673372},
//{0.06575376884422116},
//{0.06673366834170859},
//{0.06771356783919602},
//{0.06869346733668345},
//{0.06967336683417089},
//{0.07065326633165832},
//{0.07163316582914575},
//{0.07261306532663318},
//{0.07359296482412062},
//{0.07457286432160805},
//{0.07555276381909548},
//{0.07653266331658291},
//{0.07751256281407035},
//{0.07849246231155778},
//{0.07947236180904521},
//{0.08045226130653264},
//{0.08143216080402008},
//{0.08241206030150751},
//{0.08339195979899494},
//{0.08437185929648237},
//{0.0853517587939698},
//{0.08633165829145724},
//{0.08731155778894467},
//{0.0882914572864321},
//{0.08927135678391954},
//{0.09025125628140697},
//{0.0912311557788944},
//{0.09221105527638183},
//{0.09319095477386927},
//{0.0941708542713567},
//{0.09515075376884413},
//{0.09613065326633156},
//{0.097110552763819},
//{0.09809045226130643},
//{0.09907035175879386},
//{0.1000502512562813},
//{0.10103015075376873},
//{0.10201005025125616},
//{0.10298994974874359},
//{0.10396984924623102},//100
//{0.10494974874371846},
//{0.10592964824120589},
//{0.10690954773869332},
//{0.10788944723618075},
//{0.10886934673366819},
//{0.10984924623115562},
//{0.11082914572864305},
//{0.11180904522613049},
//{0.11278894472361792},
//{0.11376884422110535},
//{0.11474874371859278},
//{0.11572864321608022},
//{0.11670854271356765},
//{0.11768844221105508},
//{0.11866834170854251},
//{0.11964824120602995},
//{0.12062814070351738},
//{0.12160804020100481},
//{0.12258793969849224},
//{0.12356783919597968},
//{0.12454773869346711},
//{0.12552763819095455},
//{0.126507537688442},
//{0.12748743718592945},
//{0.1284673366834169},
//{0.12944723618090434},
//{0.1304271356783918},
//{0.13140703517587923},
//{0.13238693467336668},
//{0.13336683417085413},
//{0.13434673366834157},
//{0.13532663316582902},
//{0.13630653266331647},
//{0.1372864321608039},
//{0.13826633165829136},
//{0.1392462311557788},
//{0.14022613065326625},
//{0.1412060301507537},
//{0.14218592964824114},
//{0.1431658291457286},
//{0.14414572864321604},
//{0.14512562814070348},
//{0.14610552763819093},
//{0.14708542713567838},
//{0.14806532663316582},
//{0.14904522613065327},
//{0.15002512562814072},
//{0.15100502512562816},
//{0.1519849246231156},
//{0.15296482412060305},//150
//{0.1539447236180905},
//{0.15492462311557795},
//{0.1559045226130654},
//{0.15688442211055284},
//{0.1578643216080403},
//{0.15884422110552773},
//{0.15982412060301518},
//{0.16080402010050263},
//{0.16178391959799007},
//{0.16276381909547752},
//{0.16374371859296497},
//{0.1647236180904524},
//{0.16570351758793986},
//{0.1666834170854273},
//{0.16766331658291475},
//{0.1686432160804022},
//{0.16962311557788964},
//{0.1706030150753771},
//{0.17158291457286454},
//{0.17256281407035198},
//{0.17354271356783943},
//{0.17452261306532688},
//{0.17550251256281432},
//{0.17648241206030177},
//{0.17746231155778922},
//{0.17844221105527666},
//{0.1794221105527641},
//{0.18040201005025155},
//{0.181381909547739},
//{0.18236180904522645},
//{0.1833417085427139},
//{0.18432160804020134},
//{0.1853015075376888},
//{0.18628140703517623},
//{0.18726130653266368},
//{0.18824120603015113},
//{0.18922110552763857},
//{0.19020100502512602},
//{0.19118090452261347},
//{0.1921608040201009},//190
//	{0.2} };
//
//	double y_points[] = { 0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.01,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.02,
//0.03,
//0.01,
//0.01,
//0.06,
//0.03,
//0.06,
//0.05,
//0.06,
//0.07,
//0.08,
//0.08,
//0.03,
//0.09,
//0.1,
//0.09,
//0.08,
//0.09,
//0.09,
//0.14,
//0.08,
//0.14,
//0.13,
//0.11,
//0.21,
//0.11,
//0.19,
//0.21,
//0.21,
//0.25,
//0.24,
//0.23,
//0.16,
//0.14,
//0.16,
//0.24,
//0.25,
//0.28,
//0.19,
//0.25,
//0.17,
//0.15,
//0.15,
//0.16,
//0.15,
//0.15,
//0.2,
//0.19,
//0.2,
//0.26,
//0.18,
//0.12,
//0.18,
//0.15,
//0.12,
//0.09,
//0.16,
//0.07,
//0.07,
//0.11,
//0.1,
//0.1,
//0.19,
//0.09,
//0.12,
//0.1,
//0.08,
//0.11,
//0.07,
//0.04,
//0.11,
//0.07,
//0.07,
//0.08,
//0.11,
//0.1,
//0.04,
//0.02,
//0.07,
//0.02,
//0.04,
//0.02,
//0.06,
//0.03,
//0.02,
//0.04,
//0.05,
//0.01,
//0.0,
//0.01,
//0.05,
//0.04,
//0.03,
//0.03,
//0.06,
//0.01,
//0.02,
//0.0,
//0.06,
//0.01,
//0.01,
//0.02,
//0.02,
//0.0,
//0.0,
//0.03,
//0.01,
//0.02,
//0.01,
//0.0,
//0.0,
//0.01,
//0.01,
//0.0,
//0.0,
//0,
//0.01,
//0.0,
//0.0,
//0.01,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.02,
//0.0,
//0.01,
//0.01,
//0.0,
//0.0,
//0.01,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0,
//0.01,
//0.0,
//0.0,
//0.0,
//0.0,
//0.0 };
//
//	double xt_points[][ncolumns] = { {0.005},
//{0.005979899497487437},
//{0.006959798994974875},
//{0.007939698492462312},
//{0.00891959798994975},
//{0.009899497487437188},
//{0.010879396984924626},
//{0.011859296482412063},
//{0.012839195979899501},
//{0.013819095477386939},
//{0.014798994974874377},
//{0.015778894472361814},
//{0.01675879396984925},
//{0.017738693467336687},
//{0.018718592964824123},
//{0.01969849246231156},
//{0.020678391959798995},
//{0.02165829145728643},
//{0.022638190954773867},
//{0.023618090452261303},
//{0.02459798994974874},
//{0.025577889447236175},
//{0.02655778894472361},
//{0.027537688442211047},
//{0.028517587939698483},
//{0.02949748743718592},
//{0.030477386934673355},
//{0.031457286432160794},
//{0.032437185929648234},
//{0.03341708542713567},
//{0.03439698492462311},
//{0.03537688442211055},
//{0.03635678391959799},
//{0.03733668341708543},
//{0.03831658291457287},
//{0.03929648241206031},
//{0.04027638190954775},
//{0.04125628140703519},
//{0.04223618090452263},
//{0.04321608040201007},
//{0.04419597989949751},//40
//{0.04517587939698495},
//{0.046155778894472387},
//{0.047135678391959826},
//{0.048115577889447265},
//{0.049095477386934705},
//{0.050075376884422144},
//{0.051055276381909584},
//{0.05203517587939702},
//{0.05301507537688446},
//{0.0539949748743719},
//{0.05497487437185934},
//{0.05595477386934678},
//{0.05693467336683422},
//{0.05791457286432166},
//{0.0588944723618091},
//{0.05987437185929654},
//{0.06085427135678398},
//{0.06183417085427142},
//{0.06281407035175886},
//{0.06379396984924629},
//{0.06477386934673372},
//{0.06575376884422116},
//{0.06673366834170859},
//{0.06771356783919602},
//{0.06869346733668345},
//{0.06967336683417089},
//{0.07065326633165832},
//{0.07163316582914575},
//{0.07261306532663318},
//{0.07359296482412062},
//{0.07457286432160805},
//{0.07555276381909548},
//{0.07653266331658291},
//{0.07751256281407035},
//{0.07849246231155778},
//{0.07947236180904521},
//{0.08045226130653264},
//{0.08143216080402008},
//{0.08241206030150751},
//{0.08339195979899494},
//{0.08437185929648237},
//{0.0853517587939698},
//{0.08633165829145724},
//{0.08731155778894467},
//{0.0882914572864321},
//{0.08927135678391954},
//{0.09025125628140697},
//{0.0912311557788944},
//{0.09221105527638183},
//{0.09319095477386927},
//{0.0941708542713567},
//{0.09515075376884413},
//{0.09613065326633156},
//{0.097110552763819},
//{0.09809045226130643},
//{0.09907035175879386},
//{0.1000502512562813},
//{0.10103015075376873},
//{0.10201005025125616},
//{0.10298994974874359},
//{0.10396984924623102},//100
//{0.10494974874371846},
//{0.10592964824120589},
//{0.10690954773869332},
//{0.10788944723618075},
//{0.10886934673366819},
//{0.10984924623115562},
//{0.11082914572864305},
//{0.11180904522613049},
//{0.11278894472361792},
//{0.11376884422110535},
//{0.11474874371859278},
//{0.11572864321608022},
//{0.11670854271356765},
//{0.11768844221105508},
//{0.11866834170854251},
//{0.11964824120602995},
//{0.12062814070351738},
//{0.12160804020100481},
//{0.12258793969849224},
//{0.12356783919597968},
//{0.12454773869346711},
//{0.12552763819095455},
//{0.126507537688442},
//{0.12748743718592945},
//{0.1284673366834169},
//{0.12944723618090434},
//{0.1304271356783918},
//{0.13140703517587923},
//{0.13238693467336668},
//{0.13336683417085413},
//{0.13434673366834157},
//{0.13532663316582902},
//{0.13630653266331647},
//{0.1372864321608039},
//{0.13826633165829136},
//{0.1392462311557788},
//{0.14022613065326625},
//{0.1412060301507537},
//{0.14218592964824114},
//{0.1431658291457286},
//{0.14414572864321604},
//{0.14512562814070348},
//{0.14610552763819093},
//{0.14708542713567838},
//{0.14806532663316582},
//{0.14904522613065327},
//{0.15002512562814072},
//{0.15100502512562816},
//{0.1519849246231156},
//{0.15296482412060305},//150
//{0.1539447236180905},
//{0.15492462311557795},
//{0.1559045226130654},
//{0.15688442211055284},
//{0.1578643216080403},
//{0.15884422110552773},
//{0.15982412060301518},
//{0.16080402010050263},
//{0.16178391959799007},
//{0.16276381909547752},
//{0.16374371859296497},
//{0.1647236180904524},
//{0.16570351758793986},
//{0.1666834170854273},
//{0.16766331658291475},
//{0.1686432160804022},
//{0.16962311557788964},
//{0.1706030150753771},
//{0.17158291457286454},
//{0.17256281407035198},
//{0.17354271356783943},
//{0.17452261306532688},
//{0.17550251256281432},
//{0.17648241206030177},
//{0.17746231155778922},
//{0.17844221105527666},
//{0.1794221105527641},
//{0.18040201005025155},
//{0.181381909547739},
//{0.18236180904522645},
//{0.1833417085427139},
//{0.18432160804020134},
//{0.1853015075376888},
//{0.18628140703517623},
//{0.18726130653266368},
//{0.18824120603015113},
//{0.18922110552763857},
//{0.19020100502512602},
//{0.19118090452261347},
//{0.1921608040201009},//190
//
//	{0.2} };
//
//	vector<vector<double> > x(1), *xt;
//	vector<double> y;
//	x.resize(sizeof(x_points) / sizeof(x_points[0]));
//	y.resize(sizeof(y_points) / sizeof(y_points[0]));
//	xt = new std::vector<std::vector<double> >();
//	xt->resize(sizeof(xt_points) / sizeof(xt_points[0]));
//	for (size_t i = 0; i < x.size(); i++) {
//		x[i].resize(ncolumns);
//		for (size_t j = 0; j < ncolumns; j++) {
//			x[i][j] = x_points[i][j];
//		}
//	};
//	for (size_t i = 0; i < xt->size(); i++) {
//		(*xt)[i].resize(ncolumns);
//		for (size_t j = 0; j < ncolumns; j++) {
//			(*xt)[i][j] = xt_points[i][j];
//		}
//	};
//	copy(&y_points[0], &y_points[y.size()], y.begin());
//
//	shared_ptr<GpDataset> dataset = make_shared<GpDataset>(x, y);
//	shared_ptr<SmmcOptions> options = make_shared<SmmcOptions>(ncolumns + 1);
//	shared_ptr<SmoothedModelCheker> mc = make_shared<SmoothedModelCheker>();
//	std::vector<std::shared_ptr<Parameter> > params;
//	shared_ptr<AnalyticApproximation> approx = mc->getAnalyticApproximation(dataset, params, options);
//	std::shared_ptr<std::vector<std::vector<double> > > ptr_xt(xt);
//	shared_ptr<ProbitRegressionPosterior> result = approx->getValuesAt(ptr_xt);
//	DebugLogMatrix::printMatrix("getClassProbabilities", __LINE__, result->getClassProbabilities());
//	DebugLogMatrix::printMatrix("getLowerBound(beta)", __LINE__, result->getLowerBound(beta));
//	DebugLogMatrix::printMatrix("getUpperBound(beta)", __LINE__, result->getUpperBound(beta));
//}

int main(int argc, char *argv[]) {


    parse_cmd(argc, argv);
    // opening pdrh file
    FILE *pdrhfile = fopen(in_file.c_str(), "r");
    if (!pdrhfile) {
        cerr << "Couldn't open the file: " << endl;
        exit(EXIT_FAILURE);
    }
    // set lex to read from it instead of defaulting to STDIN:
    yyin = pdrhfile;
    // parse through the input until there is no more:
    do {
        yyparse();
    } while (!feof(yyin));

    START_EASYLOGGINGPP(argc, argv);
    el::Logger *algorithm_logger = el::Loggers::getLogger("algorithm");

    global_config.verbose_result = true;
    global_config.verbose = true;
    //global_config.bayesian_flag = true;
    omp_set_num_threads(1);


    cout << "num_samples: " << num_samples << endl;
    cout << "num_points: " << num_points << endl;
    cout << "conf: " << conf << endl;

    // the main algorithm is here

    //--------------Evaluation----------------
    vector<vector<pdrh::mode *>> paths = pdrh::get_all_paths(min_depth, max_depth);
    double ressat2 = 0, resunsat2 = 0;
    // double result = 0;

    CLOG_IF(global_config.verbose, INFO, "algorithm") << endl << "SIMPLE GP ALGORITHM";

    //initialize mu generator
    gsl_qrng *m = gsl_qrng_alloc(gsl_qrng_sobol, static_cast<unsigned int>(pdrh::rv_map.size()));
    // getting domain of mu parameters
    box mu_domain = pdrh2box::get_nondet_domain();
    CLOG_IF(global_config.verbose, INFO, "algorithm") << "mu_domain = " << mu_domain; //COUT <<ENDL;

    // initialize  random generator
    const gsl_rng_type *TT;
    gsl_rng *rr;
    gsl_rng_env_setup();
    TT = gsl_rng_default;
    rr = gsl_rng_alloc(TT);

    int NondetP = num_points; //number of points of Nondet Parameter (Mu's) ----REPLACE BY num_points!!!!!!!!!!!!!1****************************
    int pointsarray[NondetP]; //Nondet points array
    double Carray[NondetP]; // center probability
    int Sats[NondetP]; //N_s number
    int points = 0;
    int Total_samples = num_samples; //Total samples number ----REPLACE BY num_samples !!!!!!!!!!!!!!!!!!!!!******************************
    double NonDPoints[NondetP]; // Nondet points values;

    map<string, capd::interval> one_map;
    for (auto &it : pdrh::rv_map) {
        one_map.insert(make_pair(it.first, capd::interval(1, 1)));
    }
    box box_one = box(one_map);

    // main loop
    for (int l = 1; l <= NondetP; l++) {
        CLOG_IF(global_config.verbose, INFO, "algorithm") << endl << "MU count============" << l;
        double sat2 = 0, unsat2 = 0, undet2 = 0;
        double CI = 0;
        points = 1;
        double conf = global_config.qmc_conf;
        double Ca = gsl_cdf_gaussian_Pinv(1 - (1 - conf) / 2, 1);
        int SATnum = 0;

        // initialize Nondet sample
        box mu_sample = rnd::get_sobol_sample(m, mu_domain);
        CLOG_IF(global_config.verbose, INFO, "algorithm") << "mu_sample = " << mu_sample; //n
        double ss;
        ss = rnd::nond(mu_sample);
        // cout<<"!!!!!!NONDET VALUE="<<ss<<endl;
        NonDPoints[l] = ss;
        // GET MU SAPLE SINGLE VALUE
//        map<std::string, capd::interval> mu_edges;
//        mu_edges = mu_sample.get_map();
//        for (auto &it : pdrh::rv_map) {
//            mu_edges.insert(make_pair(it.first, capd::interval(0, 1)));
//        }

        // initialize Sobol generator
        gsl_qrng *q2 = gsl_qrng_alloc(gsl_qrng_sobol, static_cast<unsigned int>(pdrh::rv_map.size()));
        // getting domain of random parameters
        map<string, capd::interval> sobol_domain_map2;
        for (auto &it : pdrh::rv_map) {
            sobol_domain_map2.insert(make_pair(it.first, capd::interval(0, 1)));
        }
        box sobol_domain2(sobol_domain_map2);
        gsl_rng_set(rr, static_cast<unsigned long>(l));

#pragma omp parallel
        for (size_t i = 0; i < Total_samples; i++) {
            box sobol_sample;
            sobol_sample = rnd::get_sobol_sample(q2, sobol_domain2);
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "SOBOL SAMPLE :" << sobol_sample;
            // sample from [x1_min,x1_max]*...*[xn_min,xn_max] after applying icdf
            box GPicdf_sample = rnd::get_GPicdf(sobol_sample, mu_sample);
            //        cout << "GPicdf_sample = " << GPicdf_sample << endl;
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "GPicdf_sample :" << GPicdf_sample;
            int res;
            res = decision_procedure::evaluate_formal(paths, {GPicdf_sample, mu_sample}, "");
            // computing value of indicator function
#pragma omp critical
            {
                switch (res) {
                    // hybrid automata
                    case decision_procedure::SAT: {
                        sat2++;
                        CLOG_IF(global_config.verbose, INFO, "algorithm") << "SAT";
                        break;
                    }
                    case decision_procedure::UNSAT: {
                        unsat2++;
                        CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNSAT";
                        break;
                    }
                    case decision_procedure::UNDET: {
                        undet2++;
                        CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "UNDET";
                        break;
                    }
                    default:
                        break;
                }

                CLOG_IF(global_config.verbose, INFO, "algorithm") << "Number of SAT: " << sat2;
                CLOG_IF(global_config.verbose, INFO, "algorithm") << "Number of UNSAT: " << unsat2;
                CLOG_IF(global_config.verbose, INFO, "algorithm") << "Number of UNDET: " << undet2;

                ressat2 = sat2 / points;
                //cout << "ressat: " << ressat2 << endl;
                resunsat2 = (points - unsat2) / points;
                //cout << "resunsat: " << resunsat2 << endl;

                SATnum = sat2;

//                // write data to the "test.csv" file
//                if (sat2 != 0) {
//                    myfile << points << ";" << ressat2 << std::endl;
//                } else {
//                    myfile << points << ";" << 0 << std::endl;
//                }

                points++;
            }
        }
        points = points - 1;
        // Samplecount = Samplecount + points;
        Sats[l] = SATnum;
        pointsarray[l] = points;
        Carray[l] = resunsat2;// - global_config.qmc_acc/2 + result;
        // CLOG_IF(global_config.verbose, INFO, "algorithm") << "global_config.qmc_acc/2===" << global_config.qmc_acc / 2;
    }

    CLOG_IF(global_config.verbose, INFO, "algorithm") << "points===" << points;
    for (int l = 1; l <= NondetP; l++) {
        CLOG_IF(global_config.verbose, INFO, "algorithm") << l << "-NOND points=" << pointsarray[l] << " NOND value="
                                                          << NonDPoints[l] << " SATS=" << Sats[l] << " Center="
                                                          << Carray[l];
    }

    double Ca = gsl_cdf_gaussian_Pinv(1 - (1 - conf) / 2,
                                      1); //- REPLACE BETA !!!!!!!!!!!!!************************************
    cout << "Ca=" << Ca << endl;


    cout << "C-P approach" << endl;
    double UParray[NondetP];
    double LOarray[NondetP];
    //cout << "global_config.qmc_acc/2=" <<global_config.qmc_acc/2<< endl;
    for (int l = 1; l <= NondetP; l++) {
        if (Sats[l] == 0) {
            LOarray[l] = 0;
            UParray[l] = gsl_cdf_beta_Pinv(1 - ((1 - conf) / 2), Sats[l] + 1, Total_samples - Sats[l]);
        } else if (Sats[l] == Total_samples) {
            LOarray[l] = gsl_cdf_beta_Pinv((1 - conf) / 2, Sats[l], Total_samples - Sats[l] + 1);
            UParray[l] = 1;
        } else {
            LOarray[l] = gsl_cdf_beta_Pinv((1 - conf) / 2, Sats[l], Total_samples - Sats[l] + 1);
            UParray[l] = gsl_cdf_beta_Pinv(1 - ((1 - conf) / 2), Sats[l] + 1, Total_samples - Sats[l]);
        }
//        LOarray[l]= gsl_cdf_beta_Pinv(0.025, 10,1);
//       UParray[l]=gsl_cdf_beta_Pinv(0.975,11,0.00000000000001);
    }
    // write data to the "test.csv" file
    myfile << "Non-det pont" << ";" << "NOND value" << ";" << "CPLower" << ";" << "CPUpper" << ";" << "CPCenter"
           << "GPLower" << ";" << "GPUpper" << ";" << "GPCenter" << std::endl;
    for (int l = 1; l <= NondetP; l++) {
        CLOG_IF(global_config.verbose, INFO, "algorithm") << l << "-MU points=" << pointsarray[l] << " NOND value="
                                                          << NonDPoints[l] << " SATS=" << Sats[l] << " CPLower="
                                                          << LOarray[l] << " CPUpper="
                                                          << UParray[l] << " CPCenter="
                                                          << Carray[l];
        myfile << l << ";" << NonDPoints[l] << ";" << LOarray[l] << ";" << UParray[l] << ";" << Carray[l] << std::endl;

    }
    cout << "C-P approach end" << endl;


    //--------------Evaluation----------------

    //--------------GP----------------
    //const gsl_multimin_fminimizer_type *T = gsl_multimin_fminimizer_nmsimplex;
    //gsl_multimin_fminimizer *s = NULL;
    //s = gsl_multimin_fminimizer_alloc(T, 2);
    //gsl_multimin_fminimizer_free(s);
    //test();
    //	_CrtDumpMemoryLeaks();
    //	::system("pause");
    double beta = Ca;
    const int ncolumns = 1; // Dimention of nondet parameters (1 or 2)
    double x_points[NondetP][ncolumns];
    double y_points[NondetP];
    double xt_points[NondetP][ncolumns];


    for (int l = 0; l < NondetP; l++) {
        y_points[l] = Carray[l + 1];
        xt_points[l][ncolumns - 1] = NonDPoints[l + 1];
        x_points[l][ncolumns - 1] = NonDPoints[l + 1];
    }

    cout << "x_points" << endl;
    for (int l = 0; l < NondetP; l++) {
        cout << x_points[l][ncolumns - 1] << endl;
    }
    cout << "y_points" << endl;
    for (int l = 0; l < NondetP; l++) {
        cout << y_points[l] << endl;

    }
    cout << "xt_points" << endl;
    for (int l = 0; l < NondetP; l++) {
        cout << xt_points[l][ncolumns - 1] << endl;
    }


    vector<vector<double> > x(1), *xt;
    vector<double> y;
    x.resize(sizeof(x_points) / sizeof(x_points[0]));
    y.resize(sizeof(y_points) / sizeof(y_points[0]));
    xt = new std::vector<std::vector<double> >();
    xt->resize(sizeof(xt_points) / sizeof(xt_points[0]));
    for (size_t i = 0; i < x.size(); i++) {
        x[i].resize(ncolumns);
        for (size_t j = 0; j < ncolumns; j++) {
            x[i][j] = x_points[i][j];
        }
    };
    for (size_t i = 0; i < xt->size(); i++) {
        (*xt)[i].resize(ncolumns);
        for (size_t j = 0; j < ncolumns; j++) {
            (*xt)[i][j] = xt_points[i][j];
        }
    };
    copy(&y_points[0], &y_points[y.size()], y.begin());

    shared_ptr<GpDataset> dataset = make_shared<GpDataset>(x, y);
    shared_ptr<SmmcOptions> options = make_shared<SmmcOptions>(ncolumns + 1);
    shared_ptr<SmoothedModelCheker> mc = make_shared<SmoothedModelCheker>();
    std::vector<std::shared_ptr<Parameter> > params;
    shared_ptr<AnalyticApproximation> approx = mc->getAnalyticApproximation(dataset, params, options);
    std::shared_ptr<std::vector<std::vector<double> > > ptr_xt(xt);
    shared_ptr<ProbitRegressionPosterior> result = approx->getValuesAt(ptr_xt);
    DebugLogMatrix::printMatrix("getClassProbabilities", __LINE__, result->getClassProbabilities());
    DebugLogMatrix::printMatrix("getLowerBound(beta)", __LINE__, result->getLowerBound(beta));
    DebugLogMatrix::printMatrix("getUpperBound(beta)", __LINE__, result->getUpperBound(beta));
    //--------------GP----------------
    return 0;
}

