//
// Created by mariia on 10/09/18.
//


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

using namespace std;
std::ofstream myfile("test.csv");

capd::interval algorithm::evaluate_qmc() {
    cout << "QMC flag = " << global_config.qmc_flag << endl;
    cout << "Confidence = " << global_config.qmc_conf << endl;
    cout << "Sample size = " << global_config.qmc_sample_size << endl; //n
    cout << "Accuracy = " << global_config.qmc_acc << endl; //n
    vector<vector<pdrh::mode *>> paths = pdrh::get_all_paths();

    // initialize sobol generator
    gsl_qrng *q = gsl_qrng_alloc(gsl_qrng_sobol, static_cast<unsigned int>(pdrh::rv_map.size()));
    // getting domain of random parameters
    map<string, capd::interval> sobol_domain_map;
    for (auto &it : pdrh::rv_map) {
        sobol_domain_map.insert(make_pair(it.first, capd::interval(0, 1)));
    }
    box sobol_domain(sobol_domain_map);

    cout << endl << "SIMPLE ICDF QMC ALGORITHM" << endl;
    // initialize  random generator
    //const gsl_rng_type *TT;
    //gsl_rng *rr;
    //gsl_rng_env_setup();
    //TT = gsl_rng_default;
    //rr = gsl_rng_alloc(TT);
    //box rv_domain = measure::bounds::get_rv_domain();
    double sat = 0, unsat = 0, undet = 0;
    // main loop
    double ress;

#pragma omp parallel
#pragma omp critical
    {

        for (int i = 0; i < global_config.qmc_sample_size; i++) {
            // sobol from [0,1]*...*[0,1]
            box sobol_sample = rnd::get_sobol_sample(q, sobol_domain);
            cout << endl << "Sobol sample: " << sobol_sample << endl;
            //box random_sample = rnd::get_randomuni_sample(rr);
            //cout << "RANDOM SAMPLE " << random_sample << endl;
            //box sample = (sobol_sample + random_sample).fmod(1);
            // sample from [x1_min,x1_max]*...*[xn_min,xn_max] after applying icdf
            box icdf_sample = rnd::get_icdf(sobol_sample);
            //cout << "ICDF sample: " << icdf_sample << endl;
            // computing value of indicator function
            switch (decision_procedure::evaluate_formal(paths, {icdf_sample}, "")) {
                // hybrid automata
                case decision_procedure::SAT: {
                    sat++;
                    cout << "SAT" << endl;
                    break;
                }
                case decision_procedure::UNSAT: {
                    unsat++;
                    cout << "UNSAT" << endl;
                    break;
                }
                case decision_procedure::UNDET: {
                    undet++;
                    cout << "UNDET" << endl;
                    break;
                }
                default:
                    break;
            }
            cout << "sobol sample ==" << i + 1 << endl;
            if (sat != 0) {
                cout << "result=" << sat / (i + 1) << endl;
                ress = sat / (i + 1);
                myfile << i + 1 << ";" << ress << std::endl;
            } else {
                myfile << i + 1 << ";" << 0 << std::endl;
            }
        }
    }

    cout << "Number of SAT: " << sat << endl;
    cout << "Number of UNSAT: " << unsat << endl;
    cout << "Number of UNDET: " << undet << endl;

    cout << "[Psat, Punsat]= " << capd::interval(sat / global_config.qmc_sample_size,
                                                 (global_config.qmc_sample_size - unsat) /
                                                 global_config.qmc_sample_size) << endl;
    // Psat= Summ sat/n; Pusat=n-Summ usnat/n
    return capd::interval(sat / global_config.qmc_sample_size,
                          (global_config.qmc_sample_size - unsat) / global_config.qmc_sample_size);
}


capd::interval algorithm::evaluate_rqmc_CLT() {
    cout << "QMC flag = " << global_config.qmc_flag << endl;
    cout << "Confidence = " << global_config.qmc_conf << endl;
    cout << "Sample size = " << global_config.qmc_sample_size << endl; //n
    cout << "Accuracy = " << global_config.qmc_acc << endl; //n
    vector<vector<pdrh::mode *>> paths = pdrh::get_all_paths();
    double ressat2 = 0, resunsat2 = 0;
    double result = 0;

    cout << endl << "RQMC CLT ALGORITHM" << endl;

    // initialize  random generator
    const gsl_rng_type *TT;
    gsl_rng *rr;
    gsl_rng_env_setup();
    TT = gsl_rng_default;
    rr = gsl_rng_alloc(TT);

    int Zz = 3; //number of outer loops
    double Zresultsat = 0.0, Zresultunsat = 0.0; //Z summ
    double pointscount = 0;
    int pointsarray[Zz];
    int points = 0;
    double samplemean, stdev, samplevar, samplesq;

    map<string, capd::interval> one_map;
    for (auto &it : pdrh::rv_map) {
        one_map.insert(make_pair(it.first, capd::interval(1, 1)));
    }
    box box_one = box(one_map);

    // main loop
    for (int l = 1; l <= Zz; l++) {
        cout << endl << "Z iteration=======" << l << endl;
        double sat2 = 0, unsat2 = 0, undet2 = 0;
        double CI = 0;
        points = 1;
        double conf = global_config.qmc_conf;
        double Ca = gsl_cdf_gaussian_Pinv(1 - (1 - conf) / 2, 1);

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
        while (CI <= Ca) {
            box sobol_sample;
            sobol_sample = rnd::get_sobol_sample(q2, sobol_domain2);
            cout << "SOBOL SAMPLE :" << sobol_sample << endl;
            // sample from [x1_min,x1_max]*...*[xn_min,xn_max] after applying icdf
            box icdf_sample = rnd::get_icdf(sobol_sample); //!!!!!
            cout << "ICDF sample :" << icdf_sample << endl;
            int res;
            res = decision_procedure::evaluate_formal(paths, {icdf_sample}, "");
            // computing value of indicator function
#pragma omp critical
            {
                switch (res) {
                    // hybrid automata
                    case decision_procedure::SAT: {
                        sat2++;
                        cout << "SAT" << endl;
                        break;
                    }
                    case decision_procedure::UNSAT: {
                        unsat2++;
                        cout << "UNSAT" << endl;
                        break;
                    }
                    case decision_procedure::UNDET: {
                        undet2++;
                        cout << "UNDET" << endl;
                        break;
                    }
                    default:
                        break;
                }

                cout << "Number of SAT: " << sat2 << endl;
                cout << "Number of UNSAT: " << unsat2 << endl;
                cout << "Number of UNDET: " << undet2 << endl;

                ressat2 = sat2 / points;
                cout << "ressat: " << ressat2 << endl;
                resunsat2 = (points - unsat2) / points;
                cout << "resunsat: " << resunsat2 << endl;

                // write data to the "test.csv" file
                if (sat2 != 0) {
                    myfile << points << ";" << ressat2 << std::endl;
                } else {
                    myfile << points << ";" << 0 << std::endl;
                }

                //computing sample mean
                samplemean = sat2 * sat2 / points;
                cout << "samplemean==" << samplemean << endl;
                //computing sample variance
                samplesq = sat2;
                cout << "samplesq==" << samplesq << endl;
                if (ressat2 == 0 || ressat2 == 1)
                    samplevar = pow(pow(points, 2), -1);
                else {
                    //cout << "HERE!!!!" << endl;
                    cout << "points--" << points << endl;
                    samplevar = (samplesq - samplemean) / (points - 1);
                }
                cout << "samplevar==" << samplevar << endl;
                stdev = sqrt(samplevar);
                cout << "stdev==" << stdev << endl;

                // computing confidence intervals
                result = Ca * stdev / sqrt(points);
                CI = (global_config.qmc_acc / 2 * sqrt(points) / stdev);
                cout << "CI= " << CI << endl;
                cout << "Interval/2===" << result << endl;
                cout << "------------" << endl;
                points++;
            }
        }
        points = points - 1;
        Zresultsat = Zresultsat + ressat2;
        Zresultunsat = Zresultunsat + resunsat2;
        pointscount = pointscount + points;
        pointsarray[l] = points;
    }
    Zresultsat = Zresultsat / Zz;
    Zresultunsat = Zresultunsat / Zz;
    pointscount = pointscount / Zz;
    cout << "[Zsat, Zunsat]= " << capd::interval(Zresultsat,
                                                 Zresultunsat) << endl;
    cout << "points===" << points << endl;
    for (int l = 1; l <= Zz; l++) {
        cout << l << "-test running points==" << pointsarray[l] << endl;
    }
    cout << "pointscount===" << pointscount << endl;

//    std::ofstream myfile("test.csv");
//    //std::ofstream("test.csv", ios::app);
//    myfile << "11111111123233" << "," << 2222222222333333 << std::endl;

    return capd::interval(Zresultsat - result, Zresultunsat + result);
    // [Psat+result; Punsat-result]
}

capd::interval algorithm::evaluate_rqmc_AC() {
    cout << "QMC flag = " << global_config.qmc_flag << endl;
    cout << "Confidence = " << global_config.qmc_conf << endl;
    cout << "Sample size = " << global_config.qmc_sample_size << endl; //n
    cout << "Accuracy = " << global_config.qmc_acc << endl; //n
    vector<vector<pdrh::mode *>> paths = pdrh::get_all_paths();
    double ressat2 = 0, resunsat2 = 0;
    double result = 0;

    cout << endl << "RQMC A-C ALGORITHM" << endl;

    // initialize  random generator
    const gsl_rng_type *TT;
    gsl_rng *rr;
    gsl_rng_env_setup();
    TT = gsl_rng_default;
    rr = gsl_rng_alloc(TT);

    int Zz = 2; //number of outer loops
    double Zresultsat = 0.0, Zresultunsat = 0.0; //Z summ
    double pointscount = 0;
    int pointsarray[Zz];
    double agrest_n, agrest_p;
    int points;
    points = 0;

    map<string, capd::interval> one_map;
    for (auto &it : pdrh::rv_map) {
        one_map.insert(make_pair(it.first, capd::interval(1, 1)));
    }
    box box_one = box(one_map);

    // main loop
    for (int l = 1; l <= Zz; l++) {
        cout << "Z iteration=======" << l << endl;
        double sat2 = 0, unsat2 = 0, undet2 = 0;
        double CI = 1;
        points = 1;
        double conf = global_config.qmc_conf;
        double Ca = gsl_cdf_gaussian_Pinv(1 - (1 - conf) / 2, 1);

        // initialize Sobol generator
        gsl_qrng *q2 = gsl_qrng_alloc(gsl_qrng_sobol, static_cast<unsigned int>(pdrh::rv_map.size()));
        // getting domain of random parameters
        map<string, capd::interval> sobol_domain_map2;
        for (auto &it : pdrh::rv_map) {
            sobol_domain_map2.insert(make_pair(it.first, capd::interval(0, 1)));
        }
        box sobol_domain2(sobol_domain_map2);
        gsl_rng_set(rr, 1);

#pragma omp parallel
        while (global_config.qmc_acc / 2 <= CI) {
            // sobol from [0,1]*...*[0,1]
            box sobol_sample = rnd::get_sobol_sample(q2, sobol_domain2);
            box random_sample = rnd::get_randomuni_sample(rr);
            box sample = (sobol_sample + random_sample).fmod(1);
            //  cout << sample << endl;
            cout << "RANDOM SAMPLE :" << random_sample << endl;
            cout << "SOBOL SAMPLE :" << sobol_sample << endl;
            cout << "Sobol+RND sample :" << sample << endl;

            box icdf_sample = rnd::get_icdf(sample);
            cout << "ICDF sample: " << icdf_sample << endl;
            int res;
            res = decision_procedure::evaluate_formal(paths, {icdf_sample}, "");
            // computing value of indicator function
#pragma omp critical
            {
                switch (res) {
                    // hybrid automata
                    case decision_procedure::SAT: {
                        sat2++;
                        cout << "SAT" << endl;
                        break;
                    }
                    case decision_procedure::UNSAT: {
                        unsat2++;
                        cout << "UNSAT" << endl;
                        break;
                    }
                    case decision_procedure::UNDET: {
                        undet2++;
                        cout << "UNDET" << endl;
                        break;
                    }
                    default:
                        break;
                }
                cout << "Number of SAT: " << sat2 << endl;
                cout << "Number of UNSAT: " << unsat2 << endl;
                cout << "Number of UNDET: " << undet2 << endl;

                ressat2 = sat2 / points;
                cout << "ressat: " << ressat2 << endl;
                resunsat2 = (points - unsat2) / points;
                cout << "resunsat: " << resunsat2 << endl;

                agrest_n = points + pow(Ca, 2);
                agrest_p = pow(agrest_n, -1) * (sat2 + 0.5 * pow(Ca, 2));
                //CI = (global_config.qmc_acc / 2) / (pow(agrest_n, -0.5) * sqrt(agrest_p * (1 - agrest_p)));
                CI = Ca * (pow(agrest_n, -0.5) * sqrt(agrest_p * (1 - agrest_p)));
                cout << "Interval/2===" << CI << endl;
                result = CI;
                cout << "------------" << endl;
                points++;
            }
        }
        points = points - 1;
        Zresultsat = Zresultsat + ressat2;
        Zresultunsat = Zresultunsat + resunsat2;
        pointscount = pointscount + points;
        pointsarray[l] = points;
    }
    Zresultsat = Zresultsat / Zz;
    Zresultunsat = Zresultunsat / Zz;
    pointscount = pointscount / Zz;
    cout << "[Zsat, Zunsat]= " << capd::interval(Zresultsat,
                                                 Zresultunsat) << endl;
    cout << "points===" << points << endl;
    for (int l = 1; l <= Zz; l++) {
        cout << l << "-test running points==" << pointsarray[l] << endl;
    }
    cout << "pointscount===" << pointscount << endl;
    return capd::interval(Zresultsat - result, Zresultunsat + result);
    // [Psat+result; Punsat-result]
}


capd::interval algorithm::evaluate_rqmc_Will() {
    cout << "QMC flag = " << global_config.qmc_flag << endl;
    cout << "Confidence = " << global_config.qmc_conf << endl;
    cout << "Sample size = " << global_config.qmc_sample_size << endl; //n
    cout << "Accuracy = " << global_config.qmc_acc << endl; //n
    vector<vector<pdrh::mode *>> paths = pdrh::get_all_paths();
    double ressat2 = 0, resunsat2 = 0;
    double result = 0;

    cout << endl << "RQMC WILLSON ALGORITHM" << endl;

//        gsl_qrng *q2 = gsl_qrng_alloc(gsl_qrng_sobol, static_cast<unsigned int>(pdrh::rv_map.size()));
//        // getting domain of random parameters
//        map<string, capd::interval> sobol_domain_map2;
//        for (auto &it : pdrh::rv_map) {
//            sobol_domain_map2.insert(make_pair(it.first, capd::interval(0, 1)));
//        }
//        box sobol_domain2(sobol_domain_map2);

    // initialize  random generator
    const gsl_rng_type *TT;
    gsl_rng *rr;
    gsl_rng_env_setup();
    TT = gsl_rng_default;
    rr = gsl_rng_alloc(TT);

    int Zz = 3; //number of outer loops
    double Zresultsat = 0.0, Zresultunsat = 0.0; //Z summ
    double pointscount = 0;
    int pointsarray[Zz];
    int points;
    points = 0;

    map<string, capd::interval> one_map;
    for (auto &it : pdrh::rv_map) {
        one_map.insert(make_pair(it.first, capd::interval(1, 1)));
    }
    box box_one = box(one_map);


    // main loop
    for (int l = 1; l <= Zz; l++) {
        cout << "Z iteration=======" << l << endl;
        double sat2 = 0, unsat2 = 0, undet2 = 0;
        double CI = 1;
        points = 1;
        double conf = global_config.qmc_conf;
        double Ca = gsl_cdf_gaussian_Pinv(1 - (1 - conf) / 2, 1);

        // initialize Sobol generator
        gsl_qrng *q2 = gsl_qrng_alloc(gsl_qrng_sobol, static_cast<unsigned int>(pdrh::rv_map.size()));
        // getting domain of random parameters
        map<string, capd::interval> sobol_domain_map2;
        for (auto &it : pdrh::rv_map) {
            sobol_domain_map2.insert(make_pair(it.first, capd::interval(0, 1)));
        }
        box sobol_domain2(sobol_domain_map2);
        gsl_rng_set(rr, 1);

#pragma omp parallel
        while (global_config.qmc_acc / 2 <= CI) {
            // sobol from [0,1]*...*[0,1]
            box sobol_sample = rnd::get_sobol_sample(q2, sobol_domain2);
            box random_sample = rnd::get_randomuni_sample(rr);
            box sample = (sobol_sample + random_sample).fmod(1);
            //  cout << sample << endl;
            cout << "Sobol+RND sample :" << sample << endl;

            box icdf_sample = rnd::get_icdf(sample); //!!!!!!!!
            cout << "ICDF sample :" << icdf_sample << endl;
            int res;
            res = decision_procedure::evaluate_formal(paths, {icdf_sample}, "");
            // computing value of indicator function
#pragma omp critical
            {
                switch (res) {
                    // hybrid automata
                    case decision_procedure::SAT: {
                        sat2++;
                        cout << "SAT" << endl;
                        break;
                    }
                    case decision_procedure::UNSAT: {
                        unsat2++;
                        cout << "UNSAT" << endl;
                        break;
                    }
                    case decision_procedure::UNDET: {
                        undet2++;
                        cout << "UNDET" << endl;
                        break;
                    }
                    default:
                        break;
                }
                cout << "Number of SAT: " << sat2 << endl;
                cout << "Number of UNSAT: " << unsat2 << endl;
                cout << "Number of UNDET: " << undet2 << endl;

                ressat2 = sat2 / points;
                cout << "ressat: " << ressat2 << endl;
                resunsat2 = (points - unsat2) / points;
                cout << "resunsat: " << resunsat2 << endl;

                CI = (Ca * sqrt(points)) / (points + pow(Ca, 2)) *
                     sqrt(ressat2 * (1 - ressat2) + pow(Ca, 2) / (4 * points));
                cout << "Interval/2===" << CI << endl;
                result = CI;
                cout << "------------" << endl;
                points++;
            }
        }
        points = points - 1;
        cout << "unsat2: " << unsat2 << endl;
        cout << "points " << points << endl;
        Zresultsat = Zresultsat + (sat2 + pow(Ca, 2) / 2) / (points + pow(Ca, 2));
        Zresultunsat = Zresultunsat + ((points - unsat2) + pow(Ca, 2) / 2) / (points + pow(Ca, 2));
        pointscount = pointscount + points;
        pointsarray[l] = points;
    }
    Zresultsat = Zresultsat / Zz;
    //cout << "Zresultsat: " << Zresultsat << endl;
    Zresultunsat = Zresultunsat / Zz;
    pointscount = pointscount / Zz;
    cout << "[Zsat, Zunsat]= " << capd::interval(Zresultsat,
                                                 Zresultunsat) << endl;

    cout << "points===" << points << endl;
    for (int l = 1; l <= Zz; l++) {
        cout << l << "-test running points==" << pointsarray[l] << endl;
    }
    cout << "pointscount===" << pointscount << endl;
    return capd::interval(Zresultsat - result, Zresultunsat + result);
    // [Psat+result; Punsat-result]

}

capd::interval algorithm::evaluate_rqmc_Log() {
    cout << "QMC flag = " << global_config.qmc_flag << endl;
    cout << "Confidence = " << global_config.qmc_conf << endl;
    cout << "Sample size = " << global_config.qmc_sample_size << endl; //n
    cout << "Accuracy = " << global_config.qmc_acc << endl; //n
    vector<vector<pdrh::mode *>> paths = pdrh::get_all_paths();
    double ressat2 = 0, resunsat2 = 0;

    cout << endl << "RQMC LOGIT ALGORITHM" << endl;

    // initialize  random generator
    const gsl_rng_type *TT;
    gsl_rng *rr;
    gsl_rng_env_setup();
    TT = gsl_rng_default;
    rr = gsl_rng_alloc(TT);

    int Zz = 4; //number of outer loops
    double Zresultsat = 0.0, Zresultunsat = 0.0; //Z summ
    double pointscount = 0;
    int pointsarray[Zz];
    double logit_u, logit_l, Lambda, Var_Lambda;
    logit_l = 0;
    logit_u = 0;
    int points;
    points = 0;

    map<string, capd::interval> one_map;
    for (auto &it : pdrh::rv_map) {
        one_map.insert(make_pair(it.first, capd::interval(1, 1)));
    }
    box box_one = box(one_map);

    // main loop
    for (int l = 1; l <= Zz; l++) {
        cout << "Z iteration=======" << l << endl;
        double sat2 = 0, unsat2 = 0, undet2 = 0;
        double CI = 1;
        points = 1;
        double conf = global_config.qmc_conf;
        double Ca = gsl_cdf_gaussian_Pinv(1 - (1 - conf) / 2, 1);

        // initialize Sobol generator
        gsl_qrng *q2 = gsl_qrng_alloc(gsl_qrng_sobol, static_cast<unsigned int>(pdrh::rv_map.size()));
        // getting domain of random parameters
        map<string, capd::interval> sobol_domain_map2;
        for (auto &it : pdrh::rv_map) {
            sobol_domain_map2.insert(make_pair(it.first, capd::interval(0, 1)));
        }
        box sobol_domain2(sobol_domain_map2);
        gsl_rng_set(rr, 1);
#pragma omp parallel
        while (global_config.qmc_acc / 2 <= CI) {
            // sobol from [0,1]*...*[0,1]
            box sobol_sample;
            sobol_sample = rnd::get_sobol_sample(q2, sobol_domain2);
            box random_sample = rnd::get_randomuni_sample(rr);
            box sample = (sobol_sample + random_sample).fmod(1);
            //  cout << sample << endl;
            cout << "Sobol+RND sample :" << sample << endl;
            box icdf_sample = rnd::get_icdf(sample);
            cout << "ICDF sample :" << icdf_sample << endl;
            int res;
            res = decision_procedure::evaluate_formal(paths, {icdf_sample}, "");
            // computing value of indicator function
#pragma omp critical
            {
                switch (res) {
                    // hybrid automata
                    case decision_procedure::SAT: {
                        sat2++;
                        cout << "SAT" << endl;
                        break;
                    }
                    case decision_procedure::UNSAT: {
                        unsat2++;
                        cout << "UNSAT" << endl;
                        break;
                    }
                    case decision_procedure::UNDET: {
                        undet2++;
                        cout << "UNDET" << endl;
                        break;
                    }
                    default:
                        break;
                }
                cout << "Number of SAT: " << sat2 << endl;
                cout << "Number of UNSAT: " << unsat2 << endl;
                cout << "Number of UNDET: " << undet2 << endl;

                ressat2 = sat2 / points;
                cout << "ressat: " << ressat2 << endl;
                resunsat2 = (points - unsat2) / points;
                cout << "resunsat: " << resunsat2 << endl;

                if (points == 1) {
                    Lambda = log((sat2 + 0.5) / (points - sat2 + 0.5));
                    //  Var_Lambda = 1/pow(points,2) ;
                    Var_Lambda = 2 / ((sat2 + 0.5) * (2 - (sat2 + 0.5)));
                } else if (ressat2 == 0 or ressat2 == 1) {
                    Lambda = log((sat2 + 0.5) / (points - sat2 + 0.5));
                    cout << "Lambda= " << Lambda << endl;
                    Var_Lambda = ((points + 1) * (points + 2)) / (points * (sat2 + 1) * (points - sat2 + 1));
                } else {
                    Lambda = log(sat2 / (points - sat2));
                    Var_Lambda = points / (sat2 * (points - sat2));
                }
                cout << "Lambda= " << Lambda << endl;
                cout << "Var_Lambda= " << Var_Lambda << endl;
                logit_u = exp(Lambda + Ca * sqrt(Var_Lambda)) / (1 + exp(Lambda + Ca * sqrt(Var_Lambda)));
                logit_l = exp(Lambda - Ca * sqrt(Var_Lambda)) / (1 + exp(Lambda - Ca * sqrt(Var_Lambda)));
                cout << "logit_u= " << logit_u << endl;
                cout << "logit_l= " << logit_l << endl;
                CI = (logit_u - logit_l) / 2;
                cout << "Interval/2===" << CI << endl;
                cout << "------------" << endl;
                points++;
            }
        }
        points = points - 1;
        cout << "unsat2: " << unsat2 << endl;
        cout << "points " << points << endl;
        Zresultsat = Zresultsat + ressat2;
        Zresultunsat = Zresultunsat + resunsat2;
        pointscount = pointscount + points;
        pointsarray[l] = points;
    }
    Zresultsat = Zresultsat / Zz;
    Zresultunsat = Zresultunsat / Zz;
    pointscount = pointscount / Zz;
    cout << "[Zsat, Zunsat]= " << capd::interval(Zresultsat,
                                                 Zresultunsat) << endl;
    cout << "points===" << points << endl;
    for (int l = 1; l <= Zz; l++) {
        cout << l << "-test running points==" << pointsarray[l] << endl;
    }
    cout << "pointscount===" << pointscount << endl;
    return capd::interval(logit_l, logit_u);
    // [Psat+result; Punsat-result]
}


capd::interval algorithm::evaluate_rqmc_Ans() {
    cout << "QMC flag = " << global_config.qmc_flag << endl;
    cout << "Confidence = " << global_config.qmc_conf << endl;
    cout << "Sample size = " << global_config.qmc_sample_size << endl; //n
    cout << "Accuracy = " << global_config.qmc_acc << endl; //n
    vector<vector<pdrh::mode *>> paths = pdrh::get_all_paths();
    double ressat2 = 0, resunsat2 = 0;

    cout << endl << "RQMC ANSCOMBE ALGORITHM" << endl;

    // initialize  random generator
    const gsl_rng_type *TT;
    gsl_rng *rr;
    gsl_rng_env_setup();
    TT = gsl_rng_default;
    rr = gsl_rng_alloc(TT);

    int Zz = 5; //number of outer loops
    double Zresultsat = 0.0, Zresultunsat = 0.0; //Z summ
    double pointscount = 0;
    int pointsarray[Zz];
    double logit_u, logit_l, Lambda, Var_Lambda;
    logit_u = 0;
    logit_l = 0;
    int points;
    points = 0;

    map<string, capd::interval> one_map;
    for (auto &it : pdrh::rv_map) {
        one_map.insert(make_pair(it.first, capd::interval(1, 1)));
    }
    box box_one = box(one_map);

    // main loop
    for (int l = 1; l <= Zz; l++) {
        cout << "Z iteration=======" << l << endl;
        double sat2 = 0, unsat2 = 0, undet2 = 0;
        double CI = 1;
        points = 1;
        double conf = global_config.qmc_conf;
        double Ca = gsl_cdf_gaussian_Pinv(1 - (1 - conf) / 2, 1);

        // initialize Sobol generator
        gsl_qrng *q2 = gsl_qrng_alloc(gsl_qrng_sobol, static_cast<unsigned int>(pdrh::rv_map.size()));
        // getting domain of random parameters
        map<string, capd::interval> sobol_domain_map2;
        map<std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>, std::tuple<pdrh::node *, pdrh::node *, pdrh::node *, pdrh::node *>>::iterator it;
        for (it = pdrh::rv_map.begin(); it != pdrh::rv_map.end(); it++) {
            sobol_domain_map2.insert(make_pair(it->first, capd::interval(0, 1)));
        }
        box sobol_domain2(sobol_domain_map2);
        gsl_rng_set(rr, 1);

#pragma omp parallel
        while (global_config.qmc_acc / 2 <= CI) {
            // sobol from [0,1]*...*[0,1]
            box sobol_sample;
            sobol_sample = rnd::get_sobol_sample(q2, sobol_domain2);
            box random_sample = rnd::get_randomuni_sample(rr);
            box sample = (sobol_sample + random_sample).fmod(1);
            //  cout << sample << endl;
            cout << "Sobol+RND sample :" << sample << endl;

            box icdf_sample = rnd::get_icdf(sample); //!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
            cout << "ICDF sample :" << icdf_sample << endl;
            int res;
            res = decision_procedure::evaluate_formal(paths, {icdf_sample}, "");
            // computing value of indicator function
#pragma omp critical
            {
                switch (res) {
                    // hybrid automata
                    case decision_procedure::SAT: {
                        sat2++;
                        cout << "SAT" << endl;
                        break;
                    }
                    case decision_procedure::UNSAT: {
                        unsat2++;
                        cout << "UNSAT" << endl;
                        break;
                    }
                    case decision_procedure::UNDET: {
                        undet2++;
                        cout << "UNDET" << endl;
                        break;
                    }
                    default:
                        break;
                }
                cout << "Number of SAT: " << sat2 << endl;
                cout << "Number of UNSAT: " << unsat2 << endl;
                cout << "Number of UNDET: " << undet2 << endl;

                ressat2 = sat2 / points;
                cout << "ressat: " << ressat2 << endl;
                resunsat2 = (points - unsat2) / points;
                cout << "resunsat: " << resunsat2 << endl;

                Lambda = log((sat2 + 0.5) / (points - sat2 + 0.5));
                cout << "Lambda= " << Lambda << endl;
                double r1 = (points + 1);
                //cout << "r1= " << r1 << endl;
                double r2 = (points + 2);
                //cout << "r2= " << r2 << endl;
                double r3 = points * (sat2 + 1);
                //cout << "r3= " << r3 << endl;
                double r4 = points - sat2 + 1;
                //cout << "r4= " << r4 << endl;
                Var_Lambda = (r1 * r2) / (r3 * r4);
                //Var_Lambda = ((points + 1) * (points + 2)) / (points * (sat2 + 1) * (points - sat2 + 1));
                cout << "Var_Lambda= " << Var_Lambda << endl;
                logit_u = exp(Lambda + Ca * sqrt(Var_Lambda)) / (1 + exp(Lambda + Ca * sqrt(Var_Lambda)));
                logit_l = exp(Lambda - Ca * sqrt(Var_Lambda)) / (1 + exp(Lambda - Ca * sqrt(Var_Lambda)));
                cout << "logit_u= " << logit_u << endl;
                cout << "logit_l= " << logit_l << endl;
                CI = (logit_u - logit_l) / 2;
                cout << "Interval/2===" << CI << endl;
                cout << "------------" << endl;
                points++;
            }
        }
        points = points - 1;
        cout << "unsat2: " << unsat2 << endl;
        cout << "points " << points << endl;
        Zresultsat = Zresultsat + ressat2;
        Zresultunsat = Zresultunsat + resunsat2;
        pointscount = pointscount + points;
        pointsarray[l] = points;
    }
    Zresultsat = Zresultsat / Zz;
    Zresultunsat = Zresultunsat / Zz;
    pointscount = pointscount / Zz;
    cout << "[Zsat, Zunsat]= " << capd::interval(Zresultsat,
                                                 Zresultunsat) << endl;
    cout << "points===" << points << endl;
    for (int l = 1; l <= Zz; l++) {
        cout << l << "-test running points==" << pointsarray[l] << endl;
    }
    cout << "pointscount===" << pointscount << endl;
    return capd::interval(logit_l, logit_u);
    // [Psat+result; Punsat-result]
}

capd::interval algorithm::evaluate_rqmc_Arc() {
    cout << "QMC flag = " << global_config.qmc_flag << endl;
    cout << "Confidence = " << global_config.qmc_conf << endl;
    cout << "Sample size = " << global_config.qmc_sample_size << endl; //n
    cout << "Accuracy = " << global_config.qmc_acc << endl; //n
    vector<vector<pdrh::mode *>> paths = pdrh::get_all_paths();
    double ressat2 = 0, resunsat2 = 0;

    cout << endl << "RQMC ARCSIN ALGORITHM" << endl;

    // initialize  random generator
    const gsl_rng_type *TT;
    gsl_rng *rr;
    gsl_rng_env_setup();
    TT = gsl_rng_default;
    rr = gsl_rng_alloc(TT);

    int Zz = 6; //number of outer loops
    double Zresultsat = 0.0, Zresultunsat = 0.0; //Z summ
    double pointscount = 0;
    int pointsarray[Zz];
    double arc_p;
    double arc_u = 0;
    double arc_l = 0;
    int points;
    points = 0;

    map<string, capd::interval> one_map;
    for (auto &it : pdrh::rv_map) {
        one_map.insert(make_pair(it.first, capd::interval(1, 1)));
    }
    box box_one = box(one_map);

    // main loop
    for (int l = 1; l <= Zz; l++) {
        cout << "Z iteration=======" << l << endl;
        double sat2 = 0, unsat2 = 0, undet2 = 0;
        double CI = 1;
        points = 1;
        double conf = global_config.qmc_conf;
        double Ca = gsl_cdf_gaussian_Pinv(1 - (1 - conf) / 2, 1);
        // initialize Sobol generator
        gsl_qrng *q2 = gsl_qrng_alloc(gsl_qrng_sobol, static_cast<unsigned int>(pdrh::rv_map.size()));
        // getting domain of random parameters
        map<string, capd::interval> sobol_domain_map2;
        for (auto &it : pdrh::rv_map) {
            sobol_domain_map2.insert(make_pair(it.first, capd::interval(0, 1)));
        }
        box sobol_domain2(sobol_domain_map2);
        gsl_rng_set(rr, 1);
#pragma omp parallel
        while (global_config.qmc_acc / 2 <= CI) {
            // sobol from [0,1]*...*[0,1]
            box sobol_sample;
            sobol_sample = rnd::get_sobol_sample(q2, sobol_domain2);
            box random_sample = rnd::get_randomuni_sample(rr);
            box sample = (sobol_sample + random_sample).fmod(1);
            //  cout << sample << endl;
            cout << "Sobol+RND sample :" << sample << endl;

            box icdf_sample = rnd::get_icdf(sample);
            cout << "ICDF sample : " << icdf_sample << endl;
            int res;
            res = decision_procedure::evaluate_formal(paths, {icdf_sample}, "");
            // computing value of indicator function
#pragma omp critical
            {
                switch (res) {
                    // hybrid automata
                    case decision_procedure::SAT: {
                        sat2++;
                        cout << "SAT" << endl;
                        break;
                    }
                    case decision_procedure::UNSAT: {
                        unsat2++;
                        cout << "UNSAT" << endl;
                        break;
                    }
                    case decision_procedure::UNDET: {
                        undet2++;
                        cout << "UNDET" << endl;
                        break;
                    }
                    default:
                        break;
                }
                cout << "Number of SAT: " << sat2 << endl;
                cout << "Number of UNSAT: " << unsat2 << endl;
                cout << "Number of UNDET: " << undet2 << endl;

                ressat2 = sat2 / points;
                cout << "ressat: " << ressat2 << endl;
                resunsat2 = (points - unsat2) / points;
                cout << "resunsat: " << resunsat2 << endl;

                arc_p = (sat2 + 0.375) / (points + 0.75);
                cout << "arc_p= " << arc_p << endl;
                arc_l = pow(sin(asin(sqrt(arc_p))) - Ca / (2 * sqrt(points)), 2);
                arc_u = pow(sin(asin(sqrt(arc_p))) + Ca / (2 * sqrt(points)), 2);
                cout << "arc_l= " << arc_l << endl;
                cout << "arc_u= " << arc_u << endl;
                CI = (arc_u - arc_l) / 2;
                cout << "Interval/2===" << CI << endl;
                cout << "------------" << endl;
                points++;
            }
        }
        points = points - 1;
        cout << "unsat2: " << unsat2 << endl;
        cout << "points " << points << endl;
        Zresultsat = Zresultsat + ressat2;
        Zresultunsat = Zresultunsat + resunsat2;
        pointscount = pointscount + points;
        pointsarray[l] = points;
    }
    Zresultsat = Zresultsat / Zz;
    Zresultunsat = Zresultunsat / Zz;
    pointscount = pointscount / Zz;
    cout << "[Zsat, Zunsat]= " << capd::interval(Zresultsat,
                                                 Zresultunsat) << endl;
    //cout << "resultU===" << resultU << endl;
    cout << "points===" << points << endl;
    for (int l = 1; l <= Zz; l++) {
        cout << l << "-test running points==" << pointsarray[l] << endl;
    }
    cout << "pointscount===" << pointscount << endl;
    return capd::interval(arc_l, arc_u);
    // [Psat+result; Punsat-result]
}

capd::interval algorithm::evaluate_Qint() {
    cout << "QMC flag = " << global_config.qmc_flag << endl;
    cout << "Confidence = " << global_config.qmc_conf << endl;
    cout << "Sample size = " << global_config.qmc_sample_size << endl; //n
    cout << "Accuracy = " << global_config.qmc_acc << endl; //n
    vector<vector<pdrh::mode *>> paths = pdrh::get_all_paths();
    double ressat2 = 0, resunsat2 = 0;
    double result = 0;

    cout << endl << "QMC QINT ALGORITHM" << endl;

    //Sobol generator
    gsl_qrng *q2 = gsl_qrng_alloc(gsl_qrng_sobol, static_cast<unsigned int>(pdrh::rv_map.size()));
    map<string, capd::interval> sobol_domain_map2;
    for (auto &it : pdrh::rv_map) {
        sobol_domain_map2.insert(make_pair(it.first, capd::interval(0, 1)));
    }
    box sobol_domain2(sobol_domain_map2);
    std::vector<double> fvals;
    std::vector<int> maps;

    // initialize  random generator
    const gsl_rng_type *TT;
    gsl_rng *rr;
    gsl_rng_env_setup();
    TT = gsl_rng_default;
    rr = gsl_rng_alloc(TT);

    int Zz = 7; //number of outer loops
    double Zresultsat = 0.0, Zresultunsat = 0.0; //Z summ
    double pointscount = 0;
    int pointsarray[Zz];
    int points;
    points = 0;

    map<string, capd::interval> one_map;
    for (auto &it : pdrh::rv_map) {
        one_map.insert(make_pair(it.first, capd::interval(1, 1)));
    }
    box box_one = box(one_map);

    // main loop
    for (int l = 1; l <= Zz; l++) {
        cout << "Z iteration=======" << l << endl;
        double sat2 = 0, unsat2 = 0, undet2 = 0;
        double CI;
        //CI = 1;
        points = 1;
        double conf = global_config.qmc_conf;
        double Ca = gsl_cdf_gaussian_Pinv(1 - (1 - conf) / 2, 1);
        gsl_rng_set(rr, static_cast<unsigned long>(l));
#pragma omp parallel
        cout << "points==" << global_config.qmc_sample_size << endl;
        //    for (int i = 0; i < global_config.qmc_sample_size; i++) {
        for (int i = 0; i < 20; i++) {
            // sobol from [0,1]*...*[0,1]
            box sobol_sample = rnd::get_sobol_sample(q2, sobol_domain2);
            cout << "Sobol sample: " << sobol_sample << endl;
            // sample from [x1_min,x1_max]*...*[xn_min,xn_max] after applying icdf
            box icdf_sample = rnd::get_icdf(sobol_sample);
            cout << "ICDF sample: " << icdf_sample << endl;

            //qint---------------------------------------------------
            cout << endl;
            double ss = 0;
            std::vector<double> v;
            ss = rnd::sobol_vector(sobol_sample);
            cout << "ss: " << ss << endl;
            cout << "Vector[" << i << "]" << endl;
            for (int f = 0; f < 2; f++)            //f<2 - 2- number of dimentions!!
                v.push_back(ss);
            for (auto &item : v)
                std::cout << "element - " << item << "\n";
            int s = 2;
            unsigned long d;
            d = static_cast<int>(v.size());
            cout << endl << "dimentions=" << d << endl;
            std::vector<int> partTimes;
            partTimes.reserve(d);
            std::vector<int> binaryIndex;
            binaryIndex.reserve(d);
            int fs;
            fs = static_cast<int>(global_config.qmc_sample_size);
            maps.reserve(static_cast<unsigned long>(fs)); //N???
            int index1 = 0;
            auto dv = std::div(s, static_cast<int>(d));
            int a = dv.quot; //0 zeloe
            // cout << endl << "dv.quot=" << a<<endl;
            int b = dv.rem;  //1/5 ostatok
            // cout << endl << "dv.rem=" <<b<<endl;

            for (auto pi = 0; pi < d; pi++) {
                (pi < b) ? partTimes.push_back(a + 1) : partTimes.push_back(a);
                binaryIndex.push_back(static_cast<int &&>(floor(v[pi] * pow(2, partTimes[pi]))));

                double sum;
                sum = 0;
                for (int partTime : partTimes) {
                    sum += partTime;
                }
                std::cout << "\n" << "sum1-" << sum << "\n";
                index1 += binaryIndex[pi] * pow(2, s - sum);
                std::cout << "\n" << "index1-" << index1 << "\n";
                maps.push_back(index1);
            }
            std::cout << "\n" << "maps.size()=" << maps.size() << "\n";
            for (int &map : maps)
                std::cout << "elementmaps=" << map << "\n";
            cout << endl;

            //qint---------------------------------------------------

            int res;
            res = decision_procedure::evaluate_formal(paths, {icdf_sample}, "");
            // computing value of indicator function

#pragma omp critical
            {
                switch (res) {
                    // hybrid automata
                    case decision_procedure::SAT: {
                        sat2++;
                        cout << "SAT" << endl;
                        fvals.push_back(1);
                        break;
                    }
                    case decision_procedure::UNSAT: {
                        unsat2++;
                        cout << "UNSAT" << endl;
                        fvals.push_back(0);
                        break;
                    }
                    case decision_procedure::UNDET: {
                        undet2++;
                        cout << "UNDET" << endl;
                        break;
                    }
                    default:
                        break;
                }

                cout << "Number of SAT: " << sat2 << endl;
                cout << "Number of UNSAT: " << unsat2 << endl;
                cout << "Number of UNDET: " << undet2 << endl;

                ressat2 = sat2 / points;
                cout << "ressat2: " << ressat2 << endl;
                resunsat2 = (points - unsat2) / points;
                cout << "resunsat2: " << resunsat2 << endl;

                /* file writing
               std::ofstream("test.csv", ios::app);
              //myfile << i << "," << i << std::endl;
                if (sat2!=0){

              myfile << points << ";" << ressat2 << std::endl;
                }
                else{
              myfile << points << ";" << 0 << std::endl;
                }
                 */
                CI = (Ca * sqrt(points)) / (points + pow(Ca, 2)) *
                     sqrt(ressat2 * (1 - ressat2) + pow(Ca, 2) / (4 * points));
                //  cout << "CI= " << CI << endl;
                result = CI;
                // cout << "------------" << endl;
                points++;
            }
        }
        //qint-----------------------------------------------------------------
        std::cout << "\n" << "FVALS" << "\n"; //znacheniya funkzii v tochkah
        for (double &fval : fvals)
            std::cout << "element - " << fval << "\n";
        int kParam = 5;                                      //k parameter!
        int sParam = 2;
        int multiplier = 3;
        for (int k = 1; k <= kParam; k++) {
            // ignore k=1, variance estimate is often 0    //!!!
            if (k == 1) continue;
            // AddBorderStep(k, fvals);
            auto NSets = static_cast<int>(pow(2, sParam));
            std::vector<double> alphas;
            alphas.reserve(static_cast<unsigned long>(NSets));
            int N = k * NSets;
            std::cout << "N - " << N << "\n";
            double meanN = 0;
            double meanSqN = 0;
            double ssAlpha = 0;

            for (int j = 0; j < NSets; j++) {
                alphas.push_back(0);
            }
            // computing mean values for each group and total
            for (int i = 0; i < N; i++) {
                std::cout << "\n" << "maps[" << i << "]" << maps[i] << "\n";
                alphas[maps[i]] += fvals[i] / N;            ///maps here
                meanN += fvals[i] / N;
                meanSqN += fvals[i] * fvals[i] / N;
            }
            std::cout << "\n" << "meanN=" << meanN << "\n";
            std::cout << "\n" << "meanSqN=" << meanSqN << "\n";
            // sum of squared pairwise differences
            for (int i = 0; i < NSets; i++) {
                for (int j = i; j < NSets; j++) {
                    ssAlpha += (alphas[i] - alphas[j]) * (alphas[i] - alphas[j]);
                }
            }
            std::cout << "\n" << "ssAlpha=" << ssAlpha << "\n";
            // no border prior to N
            double varEstimMC = (meanSqN - meanN * meanN) / N;
            double varEstimQMC = varEstimMC - ssAlpha / N;
            std::cout << "\n" << "varEstimMC=" << varEstimMC << "\n";
            std::cout << "\n" << "varEstimQMC=" << varEstimQMC << "\n";
            double border = multiplier * sqrt(varEstimQMC);
            std::cout << "\n" << "border=" << border << "\n";
        }
        //qint-------------------------------------------------------------
        points = points - 1;
        // cout << "unsat2: " << unsat2 << endl;
        // cout << "points " << points << endl;
        Zresultsat = Zresultsat + ressat2;
        Zresultunsat = Zresultunsat + resunsat2;
        pointscount = pointscount + points;
        pointsarray[l] = points;
    }
    Zresultsat = Zresultsat / Zz;
    //cout << "Zresultsat: " << Zresultsat << endl;
    Zresultunsat = Zresultunsat / Zz;
    //pointscount = pointscount / Zz;
    cout << "[Zsat, Zunsat]= " << capd::interval(Zresultsat,
                                                 Zresultunsat) << endl;
    //cout << "resultU===" << resultU << endl;
    cout << "points===" << points << endl;
    for (int l = 1; l <= Zz; l++) {
        cout << l << "-test running points==" << pointsarray[l] << endl;
    }
    // cout << "pointscount===" << pointscount << endl;
    return capd::interval(Zresultsat - result, Zresultunsat + result);
    // [Psat+result; Punsat-result]
}


capd::interval algorithm::evaluate_mixCI() {
    cout << "QMC flag = " << global_config.qmc_flag << endl;
    cout << "Confidence = " << global_config.qmc_conf << endl;
    cout << "Sample size = " << global_config.qmc_sample_size << endl; //n
    cout << "Accuracy = " << global_config.qmc_acc << endl; //n
    vector<vector<pdrh::mode *>> paths = pdrh::get_all_paths();
    double result = 0;

    cout << endl << "ALL  ALGORITHMS" << endl;

    // initialize  random generator
    const gsl_rng_type *TT;
    gsl_rng *rr;
    gsl_rng_env_setup();
    TT = gsl_rng_default;
    rr = gsl_rng_alloc(TT);
    //gsl_rng_set(rr, std::chrono::system_clock::now().time_since_epoch()
    //box rv_domain = measure::bounds::get_rv_domain();
    int Zz = 8; //number of outer loops
    map<string, capd::interval> one_map;
    for (auto &it : pdrh::rv_map) {
        one_map.insert(make_pair(it.first, capd::interval(1, 1)));
    }
    box box_one = box(one_map);

    //CLT RESULTS
    double Zresultsat_CLT = 0.0, Zresultunsat_CLT = 0.0; //Z summ//
    double pointscount_CLT = 0;
    int pointsarray_CLT[Zz];
    int points_CLT;
    double ressat2_CLT = 0;
    double resunsat2_CLT = 0;
    double samplemean, stdev, samplevar, samplesq;
    //double samp;
    //AC RESULTS
    double Zresultsat_AC = 0.0, Zresultunsat_AC = 0.0; //Z summ//
    double pointscount_AC = 0;
    int pointsarray_AC[Zz];
    int points_AC;
    double ressat2_AC = 0;
    double resunsat2_AC = 0;
    double agrest_n, agrest_p;
    double result_AC = 0;
    //W RESULTS
    double Zresultsat_W = 0.0, Zresultunsat_W = 0.0; //Z summ//
    double pointscount_W = 0;
    int pointsarray_W[Zz];
    int points_W;
    double ressat2_W = 0;
    double resunsat2_W = 0;
    double result_W;
    result_W = 0;
    double sat2_W, unsat2_W;
    // L RESULTS
    double Zresultsat_L = 0.0, Zresultunsat_L = 0.0; //Z summ//
    double pointscount_L = 0;
    int pointsarray_L[Zz];
    int points_L;
    double ressat2_L = 0;
    double resunsat2_L = 0;
    double result_L;
    double logit_u = 0, logit_l = 0, Lambda, Var_Lambda;
    // ANS RESULTS
    double Zresultsat_ANS = 0.0, Zresultunsat_ANS = 0.0; //Z summ//
    double pointscount_ANS = 0;
    int pointsarray_ANS[Zz];
    int points_ANS;
    double ressat2_ANS = 0;
    double resunsat2_ANS = 0;;
    //double result_ANS;
    double Lambda_ANS, Var_Lambda_ANS;
    double ANS_l;
    ANS_l = 0;
    double ANS_u;
    ANS_u = 0;
    // ARC RESULTS
    double Zresultsat_ARC = 0.0, Zresultunsat_ARC = 0.0; //Z summ//
    double pointscount_ARC = 0;
    int pointsarray_ARC[Zz];
    int points_ARC;
    double ressat2_ARC = 0;
    double resunsat2_ARC = 0;
    //double result_ARC;
    //double arc_p;
    double arc_l, arc_u;
    arc_l = 0;
    arc_u = 0;

    // main loop
    for (int l = 1; l <= Zz; l++) {
        cout << "Z iteration=======" << l << endl;
        double sat2 = 0, unsat2 = 0, undet2 = 0;

        bool allresults;
        // allresults = false;

        //CLT RESULTS
        double CI_CLT;
        bool CI_CLT_result = false;
        points_CLT = 1;
        ressat2_CLT = 0;
        resunsat2_CLT = 0;
        //AC RESULTS
        double CI_AC;
        bool CI_AC_result = false;
        points_AC = 1;
        ressat2_AC = 0;
        resunsat2_AC = 0;
        //W RESULTS
        double CI_W;
        bool CI_W_result = false;
        points_W = 1;
        sat2_W = 0, unsat2_W = 0;
        //L RESULTS
        double CI_L;
        bool CI_L_result = false;
        points_L = 1;
        ressat2_L = 0;
        resunsat2_L = 0;
        logit_u = 0, logit_l = 0;
        //L RESULTS
        double CI_ANS;
        bool CI_ANS_result = false;
        points_ANS = 1;
        ressat2_ANS = 0;
        resunsat2_ANS = 0;
        ANS_u = 0, ANS_l = 0;
        //ARC RESULTS
        points_ARC = 1;
        ressat2_ARC = 0;
        resunsat2_ARC = 0;
        //arc_p = 0;
        arc_l = 0, arc_u = 0;
//h
        double conf = global_config.qmc_conf;
        double Ca = gsl_cdf_gaussian_Pinv(1 - (1 - conf) / 2, 1);

        // initialize Sobol generator
        gsl_qrng *q2 = gsl_qrng_alloc(gsl_qrng_sobol, static_cast<unsigned int>(pdrh::rv_map.size()));
        // getting domain of random parameters
        map<string, capd::interval> sobol_domain_map2;
        for (auto &it : pdrh::rv_map) {
            sobol_domain_map2.insert(make_pair(it.first, capd::interval(0, 1)));
        }
        box sobol_domain2(sobol_domain_map2);
        gsl_rng_set(rr, static_cast<unsigned long>(l));

//        // Bernoulli var
//        int bern;
//        gsl_rng *rrr = gsl_rng_alloc(gsl_rng_taus2);

#pragma omp parallel
        do {
            box sobol_sample = rnd::get_sobol_sample(q2, sobol_domain2);
            box random_sample = rnd::get_randomuni_sample(rr);
            cout << "RANDOM SAMPLE :" << random_sample << endl;
            cout << "SOBOL SAMPLE :" << sobol_sample << endl;
            box sample = (sobol_sample + random_sample).fmod(1);
            cout << "Sobol+RND sample :" << sample << endl;
            box icdf_sample = rnd::get_icdf(sample);
            cout << "ICDF sample :" << icdf_sample << endl;
            int res;
            res = decision_procedure::evaluate_formal(paths, {icdf_sample}, "");
            // computing value of indicator function
#pragma omp critical
            {
                // /*
                switch (res) {
                    //  hybrid automata
                    case decision_procedure::SAT: {
                        sat2++;
                        cout << "SAT" << endl;
                        break;
                    }
                    case decision_procedure::UNSAT: {
                        unsat2++;
                        cout << "UNSAT" << endl;
                        break;
                    }
                    case decision_procedure::UNDET: {
                        undet2++;
                        cout << "UNDET" << endl;
                        break;
                    }
                    default:
                        break;
                }
                //*/

                // bern = gsl_ran_bernoulli(rr, 0); //rr???
                // cout << "bern======" << bern << endl;
                //  if (bern == 1) sat2++;
                //  else unsat2++;

                cout << "Number of SAT: " << sat2 << endl;
                cout << "Number of UNSAT: " << unsat2 << endl;
                cout << "Number of UNDET: " << undet2 << endl;

                //  ressat2 = sat2 / points;
                // cout << "ressat2: " << ressat2 << endl;
                // resunsat2 = (points - unsat2) / points;
                // cout << "resunsat2: " << resunsat2 << endl;

                //CLT CALCULATING
                if (!CI_CLT_result) {

                    ressat2_CLT = sat2 / points_CLT;
                    cout << "ressat: " << ressat2_CLT << endl;
                    resunsat2_CLT = (points_CLT - unsat2) / points_CLT;
                    cout << "resunsat: " << resunsat2_CLT << endl;
                    //   computing sample mean
                    samplemean = sat2 * sat2 / points_CLT;
                    samplesq = sat2;
                    cout << "samplesq:" << samplesq << endl;
                    if (ressat2_CLT == 0)
                        samplevar = pow(pow(points_CLT, 2), -1); /////!!!!!!!!!!
                    else {
                        // cout << "HERE!!!" << endl;
                        cout << "Points_CLT;" << points_CLT << endl;
                        samplevar = (samplesq - samplemean) / (points_CLT - 1);
                    }
                    cout << "samplevar:" << samplevar << endl;
                    stdev = sqrt(samplevar);
                    cout << "stdev:" << stdev << endl;
                    // computing confidence intervals
                    result = Ca * stdev / sqrt(points_CLT);
                    //CI=Ca * stdev / sqrt(points);
                    CI_CLT = (global_config.qmc_acc / 2 * sqrt(points_CLT) / stdev);
                    cout << "CI_CLT:" << CI_CLT << endl;
                    cout << "Interval/2" << result << endl;
                    cout << "------------" << endl;
                    points_CLT++;
                    // cout << "Ca==" << Ca << endl;
                    if (CI_CLT >= Ca) CI_CLT_result = true;
                }

                //AC CALCULATING
                if (!CI_AC_result) {

                    ressat2_AC = sat2 / points_AC;
                    cout << "ressat2: " << ressat2_AC << endl;
                    resunsat2_AC = (points_AC - unsat2) / points_AC;
                    cout << "resunsat2: " << resunsat2_AC << endl;

                    agrest_n = points_AC + pow(Ca, 2);
                    agrest_p = pow(agrest_n, -1) * (sat2 + 0.5 * pow(Ca, 2));
                    //CI = (global_config.qmc_acc / 2) / (pow(agrest_n, -0.5) * sqrt(agrest_p * (1 - agrest_p)));
                    CI_AC = Ca * (pow(agrest_n, -0.5) * sqrt(agrest_p * (1 - agrest_p)));
                    cout << "CI_AC= " << CI_AC << endl;
                    result_AC = CI_AC;
                    cout << "------------" << endl;
                    points_AC++;
                    // cout << "Ca==" << Ca << endl;
                    if (global_config.qmc_acc / 2 >= CI_AC) CI_AC_result = true;
                }

                //W CALCULATING
                if (!CI_W_result) {

                    ressat2_W = sat2 / points_W;
                    cout << "ressat2: " << ressat2_W << endl;
                    resunsat2_W = (points_W - unsat2) / points_W;
                    cout << "resunsat2: " << resunsat2_W << endl;

                    CI_W = (Ca * sqrt(points_W)) / (points_W + pow(Ca, 2)) *
                           sqrt(ressat2_W * (1 - ressat2_W) + pow(Ca, 2) / (4 * points_W));

                    cout << "CI_W= " << CI_W << endl;
                    result_W = CI_W;
                    cout << "------------" << endl;
                    sat2_W = sat2;
                    unsat2_W = unsat2;
                    points_W++;
                    // cout << "Ca==" << Ca << endl;
                    if (global_config.qmc_acc / 2 >= CI_W) CI_W_result = true;
                }

                //L CALCULATING
                if (!CI_L_result) {

                    ressat2_L = sat2 / points_L;
                    cout << "ressat2_L: " << ressat2_L << endl;
                    resunsat2_L = (points_L - unsat2) / points_L;
                    cout << "resunsat2_L: " << resunsat2_L << endl;

                    if (points_L == 1) {
                        cout << "HERE!!!!!!" << endl;
                        Lambda = log((sat2 + 0.5) / (points_L - sat2 + 0.5));
                        //  Var_Lambda = 1/pow(points,2) ;
                        Var_Lambda = 2 / ((sat2 + 0.5) * (2 - (sat2 + 0.5)));
                    } else if (ressat2_L == 0 or ressat2_L == 1) {
                        cout << " NOW  HERE!!!!!!" << endl;
                        Lambda = log((sat2 + 0.5) / (points_L - sat2 + 0.5));
                        cout << "Lambda= " << Lambda << endl;
                        Var_Lambda =
                                ((points_L + 1) * (points_L + 2)) / (points_L * (sat2 + 1) * (points_L - sat2 + 1));
                    } else {
                        Lambda = log(sat2 / (points_L - sat2));
                        Var_Lambda = points_L / (sat2 * (points_L - sat2));
                    }
                    cout << "Lambda= " << Lambda << endl;
                    cout << "Var_Lambda= " << Var_Lambda << endl;
                    logit_u = exp(Lambda + Ca * sqrt(Var_Lambda)) / (1 + exp(Lambda + Ca * sqrt(Var_Lambda)));
                    logit_l = exp(Lambda - Ca * sqrt(Var_Lambda)) / (1 + exp(Lambda - Ca * sqrt(Var_Lambda)));
                    cout << "logit_u= " << logit_u << endl;
                    cout << "logit_l= " << logit_l << endl;
                    CI_L = (logit_u - logit_l) / 2;

                    cout << "CI_L= " << CI_L << endl;
                    result_L = CI_L;
                    cout << "------------" << endl;
                    points_L++;
                    cout << "result_L==" << result_L << endl;
                    if (global_config.qmc_acc / 2 >= CI_L) CI_L_result = true;
                }

                //ANS CALCULATING
                if (!CI_ANS_result) {

                    ressat2_ANS = sat2 / points_ANS;
                    cout << "ressat2_ANS: " << ressat2_ANS << endl;
                    resunsat2_ANS = (points_ANS - unsat2) / points_ANS;
                    cout << "resunsat2_ANS: " << resunsat2_ANS << endl;

                    Lambda_ANS = log((sat2 + 0.5) / (points_ANS - sat2 + 0.5));
                    cout << "Lambda_ANS= " << Lambda_ANS << endl;
                    double r1 = (points_ANS + 1);
                    //cout << "r1= " << r1 << endl;
                    double r2 = (points_ANS + 2);
                    //cout << "r2= " << r2 << endl;
                    double r3 = points_ANS * (sat2 + 1);
                    //cout << "r3= " << r3 << endl;
                    double r4 = points_ANS - sat2 + 1;
                    //cout << "r4= " << r4 << endl;
                    Var_Lambda_ANS = (r1 * r2) / (r3 * r4);
                    //Var_Lambda = ((points + 1) * (points + 2)) / (points * (sat2 + 1) * (points - sat2 + 1));
                    cout << "Var_Lambda_ANS= " << Var_Lambda_ANS << endl;
                    ANS_u = exp(Lambda_ANS + Ca * sqrt(Var_Lambda_ANS)) /
                            (1 + exp(Lambda_ANS + Ca * sqrt(Var_Lambda_ANS)));
                    ANS_l = exp(Lambda_ANS - Ca * sqrt(Var_Lambda_ANS)) /
                            (1 + exp(Lambda_ANS - Ca * sqrt(Var_Lambda_ANS)));
                    cout << "ANS_u= " << ANS_u << endl;
                    cout << "ANS_l= " << ANS_l << endl;
                    CI_ANS = (ANS_u - ANS_l) / 2;

                    cout << "CI_ANS= " << CI_ANS << endl;
                    cout << "------------" << endl;
                    points_ANS++;
                    // cout << "Ca==" << Ca << endl;
                    if (global_config.qmc_acc / 2 >= CI_ANS) CI_ANS_result = true;
                }
                /*
                //ARC CALCULATING
                if (CI_ARC_result == false) {

                    ressat2_ARC = sat2 / points_ARC;
                    cout << "ressat2_ARC: " << ressat2_ARC << endl;
                    resunsat2_ARC = (points_ARC - unsat2) / points_ARC;
                    cout << "resunsat2_ARC: " << resunsat2_ARC << endl;

                    arc_p = (sat2 + 0.375) / (points_ARC + 0.75);
                    cout << "arc_p= " << arc_p << endl;
                    arc_l = pow(sin(asin(sqrt(arc_p))) - Ca / (2 * sqrt(points_ARC)), 2);
                    arc_u = pow(sin(asin(sqrt(arc_p))) + Ca / (2 * sqrt(points_ARC)), 2);
                    cout << "arc_l= " << arc_l << endl;
                    cout << "arc_u= " << arc_u << endl;
                    CI_ARC = (arc_u - arc_l) / 2;

                    cout << "CI_ARC= " << CI_ARC << endl;
                    cout << "------------" << endl;
                    points_ARC++;
                    // cout << "Ca==" << Ca << endl;
                    if (global_config.qmc_acc / 2 >= CI_ARC) CI_ARC_result = true;
                }
                 */

            }
            allresults = CI_CLT_result && CI_AC_result && CI_W_result && CI_L_result &&
                         CI_ANS_result; // && CI_ARC_result;
        } while (!allresults);

        //CLT RESULTS
        points_CLT = points_CLT - 1;
        Zresultsat_CLT = Zresultsat_CLT + ressat2_CLT;
        Zresultunsat_CLT = Zresultunsat_CLT + resunsat2_CLT;
        pointscount_CLT = pointscount_CLT + points_CLT;
        pointsarray_CLT[l] = points_CLT;
        //AC RESULTS
        points_AC = points_AC - 1;
        Zresultsat_AC = Zresultsat_AC + ressat2_AC;
        Zresultunsat_AC = Zresultunsat_AC + resunsat2_AC;
        pointscount_AC = pointscount_AC + points_AC;
        pointsarray_AC[l] = points_AC;
        //WIL RESULTS
        points_W = points_W - 1;
        Zresultsat_W = Zresultsat_W + (sat2_W + pow(Ca, 2) / 2) / (points_W + pow(Ca, 2));
        Zresultunsat_W = Zresultunsat_W + ((points_W - unsat2_W) + pow(Ca, 2) / 2) / (points_W + pow(Ca, 2));
        pointscount_W = pointscount_W + points_W;
        pointsarray_W[l] = points_W;
        //L RESULTS
        points_L = points_L - 1;
        Zresultsat_L = Zresultsat_L + ressat2_L;
        Zresultunsat_L = Zresultunsat_L + resunsat2_L;
        pointscount_L = pointscount_L + points_L;
        pointsarray_L[l] = points_L;
        //ANS RESULTS
        points_ANS = points_ANS - 1;
        Zresultsat_ANS = Zresultsat_ANS + ressat2_ANS;
        Zresultunsat_ANS = Zresultunsat_ANS + resunsat2_ANS;
        pointscount_ANS = pointscount_ANS + points_ANS;
        pointsarray_ANS[l] = points_ANS;
        //ARC RESULTS
        points_ARC = points_ARC - 1;
        Zresultsat_ARC = Zresultsat_ARC + ressat2_ARC;
        Zresultunsat_ARC = Zresultunsat_ARC + resunsat2_ARC;
        pointscount_ARC = pointscount_ARC + points_ARC;
        pointsarray_ARC[l] = points_ARC;

    }
    cout << "---------------------------------------------------------" << endl;
    //CLT RESULTS
    cout << "CLT RESULTS:" << endl;
    Zresultsat_CLT = Zresultsat_CLT / Zz;
    Zresultunsat_CLT = Zresultunsat_CLT / Zz;
    pointscount_CLT = pointscount_CLT / Zz;
    cout << "[Zsat_CLT, Zunsat_CLT]= " << capd::interval(Zresultsat_CLT,
                                                         Zresultunsat_CLT) << endl;
    //cout << "points_CLT===" << points_CLT << endl;
    for (int l = 1; l <= Zz; l++) {
        cout << l << "-test running points CLT==" << pointsarray_CLT[l] << endl;
    }
    cout << "pointscount_CLT===" << pointscount_CLT << endl;

    cout << "[INTERVAL CLT]= " << capd::interval(Zresultsat_CLT - result,
                                                 Zresultunsat_CLT + result) << endl;
    cout << "---------------------------------------------------------" << endl;
    //AC RESULTS
    cout << "AGRESTI-COUL RESULTS:" << endl;
    Zresultsat_AC = Zresultsat_AC / Zz;
    Zresultunsat_AC = Zresultunsat_AC / Zz;
    pointscount_AC = pointscount_AC / Zz;
    cout << "[Zsat_AC, Zunsat_AC]= " << capd::interval(Zresultsat_AC,
                                                       Zresultunsat_AC) << endl;
    //cout << "points_CLT===" << points_CLT << endl;
    for (int l = 1; l <= Zz; l++) {
        cout << l << "-test running points AC==" << pointsarray_AC[l] << endl;
    }
    cout << "pointscount_AC===" << pointscount_AC << endl;

    cout << "[INTERVAL AC]= " << capd::interval(Zresultsat_AC - result_AC,
                                                Zresultunsat_AC + result_AC) << endl;
    cout << "---------------------------------------------------------" << endl;
    //W RESULTS
    cout << "WILSON RESULTS:" << endl;
    Zresultsat_W = Zresultsat_W / Zz;
    Zresultunsat_W = Zresultunsat_W / Zz;
    pointscount_W = pointscount_W / Zz;
    cout << "[Zsat_W, Zunsat_W]= " << capd::interval(Zresultsat_W,
                                                     Zresultunsat_W) << endl;
    //cout << "points_CLT===" << points_CLT << endl;
    for (int l = 1; l <= Zz; l++) {
        cout << l << "-test running points W==" << pointsarray_W[l] << endl;
    }
    cout << "pointscount_W===" << pointscount_W << endl;

    cout << "[INTERVAL W]= " << capd::interval(Zresultsat_W - result_W,
                                               Zresultunsat_W + result_W) << endl;
    cout << "---------------------------------------------------------" << endl;
    //L RESULTS
    cout << "LOGIT RESULTS:" << endl;
    Zresultsat_L = Zresultsat_L / Zz;
    Zresultunsat_L = Zresultunsat_L / Zz;
    pointscount_L = pointscount_L / Zz;
    cout << "[Zsat_L, Zunsat_L]= " << capd::interval(Zresultsat_L,
                                                     Zresultunsat_L) << endl;
    //cout << "points_CLT===" << points_CLT << endl;
    for (int l = 1; l <= Zz; l++) {
        cout << l << "-test running points L==" << pointsarray_L[l] << endl;
    }
    cout << "pointscount_L===" << pointscount_L << endl;

    cout << "[INTERVAL L]= " << capd::interval(logit_l,
                                               logit_u) << endl;
    cout << "---------------------------------------------------------" << endl;
    //ANS RESULTS
    cout << "ANSCOMBE RESULTS:" << endl;
    Zresultsat_ANS = Zresultsat_ANS / Zz;
    Zresultunsat_ANS = Zresultunsat_ANS / Zz;
    pointscount_ANS = pointscount_ANS / Zz;
    cout << "[Zsat_ANS, Zunsat_ANS]= " << capd::interval(Zresultsat_ANS,
                                                         Zresultunsat_ANS) << endl;
    //cout << "points_CLT===" << points_CLT << endl;
    for (int l = 1; l <= Zz; l++) {
        cout << l << "-test running points ANS==" << pointsarray_ANS[l] << endl;
    }
    cout << "pointscount_ANS===" << pointscount_ANS << endl;

    cout << "[INTERVAL ANS]= " << capd::interval(ANS_l,
                                                 ANS_u) << endl;
    cout << "---------------------------------------------------------" << endl;
    //ARC RESULTS
    cout << "ARCSINE RESULTS:" << endl;
    Zresultsat_ARC = Zresultsat_ARC / Zz;
    Zresultunsat_ARC = Zresultunsat_ARC / Zz;
    pointscount_ARC = pointscount_ARC / Zz;
    cout << "[Zsat_ARC, Zunsat_ARC]= " << capd::interval(Zresultsat_ARC,
                                                         Zresultunsat_ARC) << endl;
    //cout << "points_CLT===" << points_CLT << endl;
    for (int l = 1; l <= Zz; l++) {
        cout << l << "-test running points ARC==" << pointsarray_ARC[l] << endl;
    }
    cout << "pointscount_ARC===" << pointscount_ARC << endl;

    cout << "[INTERVAL ARC]= " << capd::interval(arc_l,
                                                 arc_u) << endl;
    cout << "---------------------------------------------------------" << endl;

    //write result into a file
    std::ofstream myfile("test.csv");
    //std::ofstream("test.csv", ios::app);
    myfile << 1111111111111 << "," << 2222222222222 << std::endl;
    myfile << 1111111111111 << "," << 2222222222222 << std::endl;
    //build/release

    return capd::interval(Zresultsat_CLT - result, Zresultunsat_CLT + result);
    // [Psat+result; Punsat-result]
}

//capd::interval algorithm::evaluate_GPmain() {
//    cout << "QMC flag = " << global_config.qmc_flag << endl;
//    cout << "Confidence = " << global_config.qmc_conf << endl;
//    cout << "Sample size = " << global_config.qmc_sample_size << endl; //n
//    cout << "Accuracy = " << global_config.qmc_acc << endl; //n
//    vector<vector<pdrh::mode *>> paths = pdrh::get_all_paths();
//
//    // initialize mu generator
//    gsl_qrng *m = gsl_qrng_alloc(gsl_qrng_sobol, static_cast<unsigned int>(pdrh::rv_map.size()));
//    // getting domain of mu parameters
//    box mu_domain = pdrh2box::get_nondet_domain();
//    cout << "mu_domain = " << mu_domain << endl; //n
//    box mu_sample = rnd::get_sobol_sample(m, mu_domain);
//    cout << "mu_sample = " << mu_sample << endl; //n
//
//    // initialize sobol generator
//    gsl_qrng *q = gsl_qrng_alloc(gsl_qrng_sobol, static_cast<unsigned int>(pdrh::rv_map.size()));
//    // getting domain of random parameters
//    map<string, capd::interval> sobol_domain_map;
//    for (auto &it : pdrh::rv_map) {
//        sobol_domain_map.insert(make_pair(it.first, capd::interval(0, 1)));
//    }
//    box sobol_domain(sobol_domain_map);
//
//    cout << endl << "SIMPLE GP ALGORITHM" << endl;
//
//    double sat = 0, unsat = 0, undet = 0;
//    // main loop
//    double ress;
//
//#pragma omp parallel
//#pragma omp critical
//    {
//
//        for (int i = 0; i < global_config.qmc_sample_size; i++) {
//            // sobol from [0,1]*...*[0,1]
//            box sobol_sample = rnd::get_sobol_sample(q, sobol_domain);
//            cout << endl << "Sobol sample: " << sobol_sample << endl;
//            box GPicdf_sample = rnd::get_GPicdf(sobol_sample, mu_sample);
//            cout << "GPicdf_sample = " << GPicdf_sample << endl;
//
//            // computing value of indicator function
//            switch (decision_procedure::evaluate_formal(paths, {GPicdf_sample}, "")) {
//                // hybrid automata
//                case decision_procedure::SAT: {
//                    sat++;
//                    cout << "SAT" << endl;
//                    break;
//                }
//                case decision_procedure::UNSAT: {
//                    unsat++;
//                    cout << "UNSAT" << endl;
//                    break;
//                }
//                case decision_procedure::UNDET: {
//                    undet++;
//                    cout << "UNDET" << endl;
//                    break;
//                }
//                default:
//                    break;
//            }
//
//            //writing to the file
//            cout << "sobol sample ==" << i + 1 << endl;
//            if (sat != 0) {
//                cout << "result=" << sat / (i + 1) << endl;
//                ress = sat / (i + 1);
//                myfile << i + 1 << ";" << ress << std::endl;
//            } else {
//                myfile << i + 1 << ";" << 0 << std::endl;
//            }
//        }
//    }
//
//    cout << "Number of SAT: " << sat << endl;
//    cout << "Number of UNSAT: " << unsat << endl;
//    cout << "Number of UNDET: " << undet << endl;
//
//    cout << "[Psat, Punsat]= " << capd::interval(sat / global_config.qmc_sample_size,
//                                                 (global_config.qmc_sample_size - unsat) /
//                                                 global_config.qmc_sample_size) << endl;
//    // Psat= Summ sat/n; Pusat=n-Summ usnat/n
//    return capd::interval(sat / global_config.qmc_sample_size,
//                          (global_config.qmc_sample_size - unsat) / global_config.qmc_sample_size);
//}

capd::interval algorithm::evaluate_GPmain() {
    CLOG_IF(global_config.verbose, INFO, "algorithm") << "QMC flag = " << global_config.qmc_flag;
    CLOG_IF(global_config.verbose, INFO, "algorithm") << "Confidence = " << global_config.qmc_conf;
    CLOG_IF(global_config.verbose, INFO, "algorithm") << "Sample size = " << global_config.qmc_sample_size; //n
    CLOG_IF(global_config.verbose, INFO, "algorithm") << "Accuracy = " << global_config.qmc_acc; //n
    vector<vector<pdrh::mode *>> paths = pdrh::get_all_paths();
    double ressat2 = 0, resunsat2 = 0;
    double result = 0;

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

    int Zz = 1; //number of Mu's
    double Zresultsat = 0.0, Zresultunsat = 0.0; //Z summ
    double pointscount = 0;
    int pointsarray[Zz];
    double UParray[Zz];
    double LOarray[Zz];
    double Carray[Zz];
    int points = 0;
    double samplemean, stdev, samplevar, samplesq;

    map<string, capd::interval> one_map;
    for (auto &it : pdrh::rv_map) {
        one_map.insert(make_pair(it.first, capd::interval(1, 1)));
    }
    box box_one = box(one_map);

    // main loop
    for (int l = 1; l <= Zz; l++) {
        CLOG_IF(global_config.verbose, INFO, "algorithm") << endl << "MU count============" << l;
        double sat2 = 0, unsat2 = 0, undet2 = 0;
        double CI = 0;
        points = 1;
        double conf = global_config.qmc_conf;
        double Ca = gsl_cdf_gaussian_Pinv(1 - (1 - conf) / 2, 1);

        // initialize Mu sample
        box mu_sample = rnd::get_sobol_sample(m, mu_domain);
        CLOG_IF(global_config.verbose, INFO, "algorithm") << "mu_sample = " << mu_sample; //n

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
        while (CI <= Ca) {
            box sobol_sample;
            sobol_sample = rnd::get_sobol_sample(q2, sobol_domain2);
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "SOBOL SAMPLE :" << sobol_sample;
            // sample from [x1_min,x1_max]*...*[xn_min,xn_max] after applying icdf
            box GPicdf_sample = rnd::get_GPicdf(sobol_sample, mu_sample);
//            cout << "GPicdf_sample = " << GPicdf_sample << endl;
            int res;
            res = decision_procedure::evaluate_formal(paths, {GPicdf_sample}, "");
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

                // write data to the "test.csv" file
                if (sat2 != 0) {
                    myfile << points << ";" << ressat2 << std::endl;
                } else {
                    myfile << points << ";" << 0 << std::endl;
                }

                //computing sample mean
                samplemean = sat2 * sat2 / points;
                //cout << "samplemean==" << samplemean << endl;
                //computing sample variance
                samplesq = sat2;
                //cout << "samplesq==" << samplesq << endl;
                if (ressat2 == 0 || ressat2 == 1)
                    //samplevar = pow(pow(points, 2), -1); //ORIGINAL
                    samplevar = pow(points, -1);
                else {
                    //cout << "HERE!!!!" << endl;
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "points--" << points;
                    samplevar = (samplesq - samplemean) / (points - 1);
                }
                //cout << "samplevar==" << samplevar << endl;
                stdev = sqrt(samplevar);
                //cout << "stdev==" << stdev << endl;

                // computing confidence intervals
                result = Ca * stdev / sqrt(points);
                CI = (global_config.qmc_acc / 2 * sqrt(points) / stdev);
                //cout << "CI= " << CI << endl;
                CLOG_IF(global_config.verbose, INFO, "algorithm") << "Interval/2===" << result;
                cout << "------------" << endl;
                points++;
            }
        }
        points = points - 1;
        Zresultsat = Zresultsat + ressat2;
        Zresultunsat = Zresultunsat + resunsat2;
        pointscount = pointscount + points;
        pointsarray[l] = points;
        UParray[l] = ressat2 + result;
        LOarray[l] = resunsat2 - result;
        Carray[l] = resunsat2;// - global_config.qmc_acc/2 + result;
        CLOG_IF(global_config.verbose, INFO, "algorithm") << "global_config.qmc_acc/2===" << global_config.qmc_acc / 2;
    }
    Zresultsat = Zresultsat / Zz;
    Zresultunsat = Zresultunsat / Zz;
    //pointscount = pointscount / Zz;
    //cout << "[Zsat, Zunsat]= " << capd::interval(Zresultsat,
    //                                            Zresultunsat) << endl;
    CLOG_IF(global_config.verbose, INFO, "algorithm") << "points===" << points;
    for (int l = 1; l <= Zz; l++) {
        CLOG_IF(global_config.verbose, INFO, "algorithm") << l << "-MU points=" << pointsarray[l] << " Lower="
                                                          << LOarray[l] << " Upper="
                                                          << UParray[l] << " Center="
                                                          << Carray[l];
    }
    //cout << "pointscount===" << pointscount << endl; //mean

    return capd::interval(Zresultsat - result, Zresultunsat + result);
    // [Psat+result; Punsat-result]
}
