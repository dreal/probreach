//
// Created by fedor on 26/12/15.
//
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include<string>

#ifndef PROBREACH_BOX_H
#define PROBREACH_BOX_H


class box {

private:
    std::map<std::string, capd::interval> edges;

public:
    box(std::map<std::string, capd::interval>);
    friend std::ostream& operator<<(std::ostream&, const box &);
    std::map<std::string, capd::interval> get_edges() const;

};


#endif //PROBREACH_BOX_H
