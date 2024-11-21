//
// Created by fedor on 26/12/15.
//
#include <capd/capdlib.h>
#include <capd/intervals/lib.h>

#ifndef PROBREACH_BOX_H
#define PROBREACH_BOX_H

class box
{
private:
  std::map<std::string, capd::interval> edges;

public:
  /// Creates a box that does not contain any intervals.
  box();

  /// Creates a box from a map, where keys represent variables names,
  /// and values contain their corresponding intervals.
  ///
  /// DISCLAIMER: an interval with end-points represented by "string" values
  ///             might be different from an interval where the same end-point
  ///             values are represented by "double".
  ///
  ///             This is due to how "string" intervals are converted 
  ///             to their "double" representation.
  ///
  ///             For example, capd::interval("0", "0") is not the same as
  ///             capd::interval(0, 0). In this case, the former is more
  ///             like [-4.94066e-324,4.94066e-324], while the latter is [0,0].
  box(std::map<std::string, capd::interval>);

  /// Constructs a box from its string representation (e.g., "a[0,1];b[-3,4];").
  box(std::string);
  box(std::vector<box>);

  /// Outputs a string representation (e.g., "a[0,1];b[-3,4];") 
  /// of the box into the specified stream.
  friend std::ostream &operator<<(std::ostream &, const box &);
  friend bool operator<(const box &, const box &);

  /// Check if two boxes are equal (i.e., the variable set is the same, and the
  /// corresponding intervals are equal).
  friend bool operator==(const box &, const box &);
  friend box operator+(const box &, const box &);
  friend box operator-(const box &, const box &);
  friend box operator*(const box &, const box &);
  friend box operator/(const box &, const box &);
  friend box operator/(const box &, double);

  /// Returns a map representation of the box, whether the map keys contain
  /// the edges names, and the map values contain the intervals
  /// representing the edges.
  std::map<std::string, capd::interval> get_map() const;

  /// Returns the list of invervals comprising the box edges.
  std::vector<capd::interval> get_intervals() const;

  /// Returns the box variables.
  std::set<std::string> get_vars() const;

  /// Returns true if the box does not have any edges.
  bool empty() const;

  /// Returns true if the given box and the current box have the same
  /// variables.
  bool compatible(box) const;
  
  /// Returns true if the given box is fully contained within the current box,
  /// and false otherwise or if the two boxes are not compatible.
  bool contains(box) const;
  
  /// Returns true if the given box intersects the current box in at least
  /// one dimension, and false if the two boxes are disjoint or not compatible.
  bool intersects(box) const;
  box get_keys_diff(box) const;
  
  /// Returns a the middle point of the box
  box mid();
  box get_stddev();
  box fmod(int);
  box sqrt();
  box log();
  double max_coordinate_value();
  double max_side_width();
  double min_side_width();

  /// Removes specified variable (together with its interval) from the box
  void erase(std::string);
};

#endif // PROBREACH_BOX_H
