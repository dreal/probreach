//
// Created by fedor on 23/01/17.
//

#include <gtest/gtest.h>
#include "node.h"
#include <cmath>

using namespace std;
using namespace pdrh;

size_t iter_num = 100000;

TEST(node_to_double_normal_distribution, mean_and_variance_check)
{
    node* mu = new node("0");
    node* sigma = new node("1");
    node* n = new node("dist_normal", {mu, sigma});
    double sample[iter_num];
    double sum = 0;
    // computing the mean value here
    for(size_t i = 0; i < iter_num; i++)
    {
        sample[i] = node_to_double(n);
        sum += sample[i];
    }
    double mean = sum / iter_num;
    // computing standard deviation here
    sum = 0;
    for(size_t i = 0; i < iter_num; i++)
    {
        sum += pow(mean - sample[i], 2);
    }
    double var = sum / iter_num;
    EXPECT_NEAR(mean, node_to_double(mu), 1e-2);
    EXPECT_NEAR(var, pow(node_to_double(sigma), 2), 1e-2);
}

TEST(node_to_double_exp_distribution, mean_and_variance_check)
{
    node *lambda = new node("2");
    node *n = new node("dist_exp", {lambda});
    double sample[iter_num];
    double sum = 0;
    // computing the mean value here
    for (size_t i = 0; i < iter_num; i++)
    {
        sample[i] = node_to_double(n);
        sum += sample[i];
    }
    double mean = sum / iter_num;
    // computing standard deviation here
    sum = 0;
    for (size_t i = 0; i < iter_num; i++)
    {
        sum += pow(mean - sample[i], 2);
    }
    double var = sum / iter_num;
    EXPECT_NEAR(mean, pow(node_to_double(lambda),-1), 1e-2);
    EXPECT_NEAR(var, pow(node_to_double(lambda),-2), 1e-2);
}

TEST(node_to_double_gamma_distribution, mean_and_variance_check)
{
    node *a = new node("2");
    node *b = new node("2");
    node *n = new node("dist_gamma", {a, b});
    double sample[iter_num];
    double sum = 0;
    // computing the mean value here
    for (size_t i = 0; i < iter_num; i++)
    {
        sample[i] = node_to_double(n);
        sum += sample[i];
    }
    double mean = sum / iter_num;
    // computing standard deviation here
    sum = 0;
    for (size_t i = 0; i < iter_num; i++)
    {
        sum += pow(mean - sample[i], 2);
    }
    double var = sum / iter_num;
    EXPECT_NEAR(mean, node_to_double(a) * node_to_double(b), 1e-1);
    EXPECT_NEAR(var, node_to_double(a) * pow(node_to_double(b), 2), 1e-1);
}

TEST(node_to_double_uniform_distribution, mean_and_variance_check)
{
    node *a = new node("0");
    node *b = new node("1");
    node *n = new node("dist_uniform", {a, b});
    double sample[iter_num];
    double sum = 0;
    // computing the mean value here
    for (size_t i = 0; i < iter_num; i++)
    {
        sample[i] = node_to_double(n);
        sum += sample[i];
    }
    double mean = sum / iter_num;
    // computing standard deviation here
    sum = 0;
    for (size_t i = 0; i < iter_num; i++)
    {
        sum += pow(mean - sample[i], 2);
    }
    double var = sum / iter_num;
    EXPECT_NEAR(mean, (node_to_double(a) + node_to_double(b)) / 2, 1e-1);
    EXPECT_NEAR(var, pow(node_to_double(b) - node_to_double(a), 2) / 12, 1e-1);
}

TEST(node_to_double_discrete_distribution, mass_test)
{
    node* v[] = {new node("0"), new node("1"), new node("2")};
    node* p[] = {new node("0.1"), new node("0.5"), new node("0.4")};

    node* val1 = new node(":", {v[0], p[0]});
    node* val2 = new node(":", {v[1], p[1]});
    node* val3 = new node(":", {v[2], p[2]});
    node* n = new node("dist_discrete", {val1, val2, val3});

    double sum[] = {0, 0, 0};
    // computing the mean value here
    for (size_t i = 0; i < iter_num; i++)
    {
        sum[(size_t)round(node_to_double(n))]++;
    }
    for(size_t i = 0; i < 3; i++)
    {
        sum[i] /= iter_num;
        EXPECT_NEAR(sum[i], node_to_double(p[i]), 1e-2);
    }
}


