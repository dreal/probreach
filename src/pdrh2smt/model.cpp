//
// Created by fedor on 03/02/17.
//

#include <sstream>
#include "model.h"
#include <algorithm>

model::model()
{

}

void model::set_time(node lhs, node rhs)
{
    /*
    if(!this->time.first.is_empty() || !this->time.second.is_empty())
    {
        throw invalid_argument("time variable should be defined only once");
    }
    */
    this->time = make_pair(lhs, rhs);
}

void model::push_var(string var, node lhs, node rhs)
{
    if(this->var_map.find(var) != this->var_map.end())
    {
        stringstream s;
        s << "variable " << var << " has already been declared";
        throw invalid_argument(s.str());
    }
    this->var_map.insert(make_pair(var, make_pair(lhs, rhs)));
}

void model::push_mode(mode md)
{
    for(mode m : this->modes)
    {
        if(m.get_id() == md.get_id())
        {
            stringstream s;
            s << "mode with id " << md.get_id() << " has already been created";
            throw invalid_argument(s.str());
        }
    }
    this->modes.push_back(md);
}

void model::push_init(int id, node pred)
{
    bool mode_exists = false;
    for(mode m : this->modes)
    {
        if(m.get_id() == id)
        {
            mode_exists = true;
        }
    }
    if(!mode_exists)
    {
        stringstream s;
        s << "mode with id " << id << " is not in the model";
    }
    this->inits.push_back(make_pair(id, pred));
}

void model::push_goal(int id, node pred)
{
    bool mode_exists = false;
    for(mode m : this->modes)
    {
        if(m.get_id() == id)
        {
            mode_exists = true;
        }
    }
    if(!mode_exists)
    {
        stringstream s;
        s << "mode with id " << id << " is not in the model";
    }
    this->goals.push_back(make_pair(id, pred));
}

bool model::var_exists(string var)
{
    return (this->var_map.find(var) != this->var_map.end());
}

void model::set_var_bounds(string var, node lhs, node rhs)
{
    remove_var(var);
    push_var(var, lhs, rhs);
}

void model::remove_var(string var)
{
    if(!var_exists(var))
    {
        stringstream s;
        s << "could not remove non-existing variable " << var;
        throw invalid_argument(s.str());
    }
    this->var_map.erase(var);
}

void model::remove_mode(int id)
{
    mode md = get_mode(id);
    this->modes.erase(find(this->modes.begin(), this->modes.end(), md));
}

void model::remove_init(int id, node prop)
{
    auto init_it = find(this->inits.begin(), this->inits.end(), pair<int, node>(id, prop));
    if(init_it == this->inits.end())
    {
        stringstream s;
        s << "could not remove non-existing init @" << id << ":" << prop.to_infix();
        throw invalid_argument(s.str());
    }
    this->inits.erase(init_it);
}

void model::remove_goal(int id, node prop)
{
    auto goal_it = find(this->goals.begin(), this->goals.end(), pair<int, node>(id, prop));
    if(goal_it == this->goals.end())
    {
        stringstream s;
        s << "could not remove non-existing init @" << id << ":" << prop.to_infix();
        throw invalid_argument(s.str());
    }
    this->goals.erase(goal_it);
}


vector<int> model::find_shortest_path()
{
    // initializing the set of paths
    vector<vector<int>> paths;
    vector<int> path;
    for (pair<int, node> i : this->inits)
    {
        for (pair<int, node> g : this->goals)
        {
            if (i.first == g.first)
            {
                return vector<int>{ i.first };
            }
            else
            {
                // pushing the initial mode to the initial path
                path.push_back(i.first);
                // pushing the initial path to the set of paths
                paths.push_back(path);
                while (!paths.empty())
                {
                    // getting the first path in the set of paths
                    path = paths.front();
                    paths.erase(paths.begin());
                    // getting the mode in the path
                    int mode_id = path.back();
                    vector<int> successors = get_mode(mode_id).get_successors();
                    // proceeding if the current mode has successors
                    if(!successors.empty())
                    {
                        // checking if one of the successors is the end mode
                        if (find(successors.begin(), successors.end(), g.first) != successors.end())
                        {
                            path.push_back(g.first);
                            paths.clear();
                            return path;
                        }
                        else
                        {
                            // iterating through the successors of the current mode
                            for (int s : successors)
                            {
                                // checking if a successor does not appear in the current path
                                if (find(path.begin(), path.end(), s) == path.end())
                                {
                                    vector<int> tmp_path = path;
                                    tmp_path.push_back(s);
                                    paths.push_back(tmp_path);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    path.clear();
    return path;
}

vector<vector<int>> model::find_all_paths_of_length(int length)
{
    // initializing the set of paths
    vector<vector<int>> paths;
    for(pair<int, node> i : this->inits)
    {
        for(pair<int, node> g : this->goals)
        {
            vector<int> path;
            path.push_back(i.first);
            // initializing the stack
            vector<vector<int>> stack;
            stack.push_back(path);
            while(!stack.empty())
            {
                // getting the first paths from the set of paths
                path = stack.front();
                stack.erase(stack.cbegin());
                // checking if the correct path of the required length is found
                if((path.back() == g.first) && (path.size() == length + 1))
                {
                    // checking if the path already exists
                    if(find(paths.begin(), paths.end(), path) == paths.end())
                    {
                        paths.push_back(path);
                    }
                }
                // proceeding only if the length of the current path is ascending then the required length
                else if(path.size() < length + 1)
                {
                    // getting the last mode in the path
                    int mode_id = path.back();
                    // getting the successors of the mode
                    vector<int> successors = get_mode(mode_id).get_successors();
                    for(int s : successors)
                    {
                        // appending the successor the current paths
                        vector<int> new_path = path;
                        new_path.push_back(s);
                        // pushing the new path to the set of the paths
                        stack.push_back(new_path);
                    }
                }
            }
        }
    }
    return paths;
}


std::ostream& operator<<(std::ostream& os, model& m)
{
    os << "VARIABLES:" << endl;
    map<string, pair<node, node>> vars = m.get_var_map();
    for(auto it = vars.begin(); it != vars.end(); it++)
    {
        os << "|   " << it->first << " [" << it->second.first.to_infix() << ", " <<
        it->second.second.to_infix() << "]" << endl;
    }
    /*
    os << "CONTINUOUS RANDOM VARIABLES:" << endl;
    for(auto it = pdrh::rv_map.cbegin(); it != pdrh::rv_map.cend(); it++)
    {
        os << "|   pdf(" << it->first << ") = " << pdrh::node_to_string_infix(get<0>(it->second)) << "  | "
        << pdrh::node_to_string_prefix(get<1>(it->second)) << " |   "
        << pdrh::node_to_string_prefix(get<2>(it->second)) << "    |   "
        << pdrh::node_to_string_prefix(get<3>(it->second)) << endl;
    }
    os << "DISCRETE RANDOM VARIABLES:" << endl;
    for(auto it = pdrh::dd_map.cbegin(); it != pdrh::dd_map.cend(); it++)
    {
        os << "|   dd(" << it->first << ") = (";
        for(auto it2 = it->second.cbegin(); it2 != it->second.cend(); it2++)
        {
            cout << pdrh::node_to_string_prefix(it2->first) << " : " << pdrh::node_to_string_prefix(it2->second) << endl;
            os << pdrh::node_to_string_prefix(it2->first) << " : " << pdrh::node_to_string_prefix(it2->second) << ", ";
        }
        os << ")" << endl;
    }
    */
    os << "TIME DOMAIN:" << endl;
    os << "|   [" << m.get_time_bounds().first.to_infix() << ", " << m.get_time_bounds().second.to_infix() << "]" << endl;
    os << "MODES:" << endl;
    for(mode md : m.get_modes())
    {
        os << "|   MODE: " << md.get_id() << ";" << endl;
        os << "|   INVARIANTS:" << endl;
        for(node n : md.get_invariants())
        {
            os << "|   |   " << n.to_infix() << endl;
        }
        os << "|   FLOW_MAP:" << endl;
        vector<string> flow_map = md.get_vars();
        for(string var : flow_map)
        {
            os << "|   " << var << " " << " [" << m.get_var_bounds(var).first.to_infix() << ", " <<
                    m.get_var_bounds(var).second.to_infix() << "]" << endl;
        }
        os << "|   ODES:" << endl;
        map<string, node> ode_map = md.get_odes();
        for(auto it = ode_map.begin(); it != ode_map.end(); it++)
        {
            os << "|   |   d[" << it->first << "]/dt = " << it->second.to_infix() << endl;
        }
        os << "|   JUMPS:" << endl;
        for(jump j : md.get_jumps())
        {
            os << "|   |   GUARD: " << j.get_guard().to_infix() << endl;
            os << "|   |   SUCCESSOR: " << j.get_id() << endl;
            os << "|   |   RESETS:" << endl;
            map<string, node> reset_map = j.get_reset_map();
            for(auto it = reset_map.begin(); it != reset_map.end(); it++)
            {
                os << "|   |   |   " << it->first << " := " << it->second.to_infix() << endl;
            }
        }
    }
    os << "INIT:" << endl;
    for(pair<int, node> s : m.get_inits())
    {
        os << "|   MODE: " << s.first << endl;
        os << "|   PROPOSITION: " << s.second.to_infix() << endl;
    }
    if(m.get_goals().size() > 0)
    {
        os << "GOAL:" << endl;
        for(pair<int, node> s : m.get_goals())
        {
            os << "|   MODE: " << s.first << endl;
            os << "|   PROPOSITION: " << s.second.to_infix() << endl;
        }
    }
    else
    {
        /*
        os << "SYNTHESIZE:" << endl;
        for(auto it = pdrh::syn_map.cbegin(); it != pdrh::syn_map.cend(); it++)
        {
            os << "|   " << it->first << " " << pdrh::node_to_string_prefix(it->second) << endl;
        }
        */
    }
    return os;
}


// getters and setters
map<string, pair<node, node>> model::get_var_map()
{
    return this->var_map;
}

pair<node, node> model::get_var_bounds(string var)
{
    map<string, pair<node, node>> vars = this->var_map;
    if(vars.find(var) != vars.end())
    {
        return vars[var];
    }
    return make_pair(node(), node());
}

pair<node, node> model::get_time_bounds()
{
    return this->time;
}

vector<mode> model::get_modes()
{
    return this->modes;
}

vector<pair<int, node>> model::get_inits()
{
    return this->inits;
}

node model::get_init(int id)
{
    vector<node> nodes;
    for(pair<int, node> i : this->inits)
    {
        if(i.first == id)
        {
            nodes.push_back(i.second);
        }
    }
    return node("or", nodes);
}

vector<pair<int, node>> model::get_goals()
{
    return this->goals;
}

node model::get_goal(int id)
{
    vector<node> nodes;
    for(pair<int, node> g : this->goals)
    {
        if(g.first == id)
        {
            nodes.push_back(g.second);
        }
    }
    return node("or", nodes);
}

mode model::get_mode(int id)
{
    for(mode md : this->modes)
    {
        if(md.get_id() == id)
        {
            return md;
        }
    }
    stringstream s;
    s << "mode with id " << id << " has not been defined";
    throw invalid_argument(s.str());
}