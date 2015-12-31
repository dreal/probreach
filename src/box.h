//
// Created by fedor on 26/12/15.
//
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>

#ifndef PROBREACH_BOX_H
#define PROBREACH_BOX_H


class box
{
protected:
    std::map<std::string, capd::interval> edges;

public:
    box();
    box(std::map<std::string, capd::interval>);
    friend std::ostream& operator<<(std::ostream&, const box &);
    std::map<std::string, capd::interval> get_map() const;
    std::vector<capd::interval> get_intervals();
    std::vector<std::string> get_vars();
};

class dd_box : public box
{
public:
    dd_box(std::map<std::string, capd::interval>);
};

class rv_box : public box
{
public:
    rv_box(std::map<std::string, capd::interval>);
    rv_box(box);
};

class nd_box : public box
{
public:
    nd_box(std::map<std::string, capd::interval>);
    nd_box(box);
};

#endif //PROBREACH_BOX_H
