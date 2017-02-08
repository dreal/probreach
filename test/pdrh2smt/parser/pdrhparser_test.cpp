//
// Created by fedor on 06/02/17.
//

#include "node.h"
#include <gtest/gtest.h>
#include "model.h"
#include "pdrhparser.hpp"
#include "smt2generator.h"

using namespace std;

TEST(pdrhparser, normal)
{
    model m = parse_pdrh("/home/fedor/probreach/model/anesthesia/anesthesia.drh");

    cout << m << endl;

    cout << "Shortest path:" << endl;
    vector<int> path = m.find_shortest_path();
    for(int i : path)
    {
        cout << i << " ";
    }
    cout << endl;

    int length = 3;
    vector<vector<int>> paths = m.find_all_paths_of_length(length);
    cout << "Paths of length " << length << endl;
    for(vector<int> p : paths)
    {
        for(int i : p)
        {
            cout << i << " ";
        }
        cout << endl;
    }

    cout << m.get_init(1).to_prefix("_0_t") << endl;

    cout << "smt2 generator:" << endl;
    cout << smt2generator::generate_reachability_formula(m) << endl;
}