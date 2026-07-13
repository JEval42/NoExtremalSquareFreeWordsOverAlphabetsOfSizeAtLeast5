/*
 * Compute the maximum mean cycle used in Lemma
 * `lem:max-mean-weight-cycles` of paper.tex.
 *
 * The program first enumerates the realisable k-tuples that form the vertex
 * set R_{S,k}.  It then constructs G_k(S), whose edges shift a tuple one
 * position to the left, and applies a tie-safe integer implementation of
 * Howard's policy-iteration algorithm.  Before reporting a result, it verifies
 * an exact cycle-and-potential certificate of optimality.
 *
 * Mathematical positions in the paper are one-based.  Positions and gaps in
 * this implementation are zero-based; lengths are unchanged.
 *
 * Usage:
 *   ./code tuple_length range_start range_end_exclusive
 *
 * The three computations used in the paper are:
 *   ./code 10  2 13   # S = {2, ..., 12}
 *   ./code 25 13 26   # S = {13, ..., 25}
 *   ./code 51 26 40   # S = {26, ..., 39}
 */

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstring>
#include <deque>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#include <numeric>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace
{

using EncodedWord = std::vector<int>;
using LengthSet = std::vector<int>;

// A vertex (S_1, ..., S_k) of G_k(S).  Each component is stored in increasing
// order because the enumeration processes the permitted lengths in order.
using RealisableTuple = std::vector<LengthSet>;

/*
 * A square constraint records the numerical part (a, ell, b) of a negative-
 * sign minimal square-completing quadruple.  The inserted letter is omitted:
 * its required value is represented by an equivalence class in EncodedWord.
 */
struct SquareConstraint {
   int square_start;
   int half_length;
   int insertion_gap;
};

using ConstraintList = std::vector<SquareConstraint>;

// ---------------------------------------------------------------------------
// Square detection in equivalence-class encodings
// ---------------------------------------------------------------------------

/*
 * A word is encoded by assigning the same integer to positions that are
 * required to contain the same letter.  The actual integer values are
 * irrelevant; only equality between positions matters.
 *
 * Rolling hashes make the repeated square tests inexpensive.  Every hash
 * match is confirmed with an exact comparison, so hash collisions cannot
 * affect the result of the computation.
 */
constexpr std::uint64_t kRollingHashBase = 0x9e3779b185ebca87ULL;

void
build_rolling_hash(const EncodedWord& word, std::vector<std::uint64_t>& prefix_hashes,
                   std::vector<std::uint64_t>& base_powers)
{
   const int word_length = static_cast<int>(word.size());
   if (static_cast<int>(prefix_hashes.size()) < word_length + 1) {
      prefix_hashes.resize(word_length + 1);
      base_powers.resize(word_length + 1);
   }

   prefix_hashes[0] = 0;
   base_powers[0] = 1;
   for (int position = 0; position < word_length; ++position) {
      const auto encoded_letter
            = static_cast<std::uint64_t>(static_cast<std::uint32_t>(word[position])) + 0x243f6a8885a308d3ULL;

      base_powers[position + 1] = base_powers[position] * kRollingHashBase;
      prefix_hashes[position + 1] = prefix_hashes[position] * kRollingHashBase + encoded_letter;
   }
}

std::uint64_t
substring_hash(const std::vector<std::uint64_t>& prefix_hashes, const std::vector<std::uint64_t>& base_powers,
               int start, int length)
{
   return prefix_hashes[start + length] - prefix_hashes[start] * base_powers[length];
}

bool
ranges_are_equal(const EncodedWord& word, int first_start, int second_start, int length)
{
   return std::memcmp(static_cast<const void*>(word.data() + first_start),
                      static_cast<const void*>(word.data() + second_start),
                      static_cast<std::size_t>(length) * sizeof(int))
          == 0;
}

bool
is_square_free(const EncodedWord& word)
{
   const int word_length = static_cast<int>(word.size());

   // Squares of half-length one are frequent and cheap to detect directly.
   for (int position = 0; position + 1 < word_length; ++position) {
      if (word[position] == word[position + 1]) {
         return false;
      }
   }

   if (word_length < 4) {
      return true;
   }

   thread_local std::vector<std::uint64_t> prefix_hashes;
   thread_local std::vector<std::uint64_t> base_powers;
   build_rolling_hash(word, prefix_hashes, base_powers);

   for (int half_length = 2; half_length <= word_length / 2; ++half_length) {
      for (int square_start = 0; square_start + 2 * half_length <= word_length; ++square_start) {
         const int second_half_start = square_start + half_length;
         if (substring_hash(prefix_hashes, base_powers, square_start, half_length)
                   == substring_hash(prefix_hashes, base_powers, second_half_start, half_length)
             && ranges_are_equal(word, square_start, second_half_start, half_length)) {
            return false;
         }
      }
   }

   return true;
}

/*
 * Return whether a target square is preceded in the minimality order by a
 * square with a shorter half-length, or by one of the same length beginning
 * further to the left.  This is precisely the obstruction to the target
 * square-completing quadruple being minimal.
 */
bool
target_square_has_preferred_competitor(const EncodedWord& word_after_insertion, int target_half_length,
                                       int target_start)
{
   const int word_length = static_cast<int>(word_after_insertion.size());

   if (target_start < 0 || target_start + 2 * target_half_length > word_length) {
      return false;
   }

   // The caller constructs the target square through equality constraints.
   // Retaining this exact check makes the routine safe to use independently.
   if (!ranges_are_equal(word_after_insertion, target_start, target_start + target_half_length, target_half_length)) {
      return false;
   }

   thread_local std::vector<std::uint64_t> prefix_hashes;
   thread_local std::vector<std::uint64_t> base_powers;
   build_rolling_hash(word_after_insertion, prefix_hashes, base_powers);

   for (int half_length = 1; half_length <= target_half_length; ++half_length) {
      for (int square_start = 0; square_start + 2 * half_length <= word_length; ++square_start) {
         const bool precedes_target = half_length < target_half_length || square_start < target_start;
         if (!precedes_target) {
            continue;
         }

         const int second_half_start = square_start + half_length;
         if (substring_hash(prefix_hashes, base_powers, square_start, half_length)
                   == substring_hash(prefix_hashes, base_powers, second_half_start, half_length)
             && ranges_are_equal(word_after_insertion, square_start, second_half_start, half_length)) {
            return true;
         }
      }
   }

   return false;
}

bool
insertion_preserves_minimality(const EncodedWord& base_word, int insertion_gap, int inserted_equivalence_class,
                               int target_half_length, int target_start)
{
   const int base_word_length = static_cast<int>(base_word.size());
   EncodedWord word_after_insertion(base_word_length + 1);

   std::copy_n(base_word.begin(), insertion_gap, word_after_insertion.begin());
   word_after_insertion[insertion_gap] = inserted_equivalence_class;
   std::copy(base_word.begin() + insertion_gap, base_word.end(), word_after_insertion.begin() + insertion_gap + 1);

   return !target_square_has_preferred_competitor(word_after_insertion, target_half_length, target_start);
}

// ---------------------------------------------------------------------------
// Equality constraints forced by square-completing insertions
// ---------------------------------------------------------------------------

class DisjointSet
{
public:
   explicit DisjointSet(int element_count) : parent_(element_count), rank_(element_count, 0)
   {
      std::iota(parent_.begin(), parent_.end(), 0);
   }

   int
   representative(int element)
   {
      int root = element;
      while (parent_[root] != root) {
         root = parent_[root];
      }

      // Compress the path so subsequent equality queries are constant-time
      // in practice.
      while (parent_[element] != element) {
         const int next_element = parent_[element];
         parent_[element] = root;
         element = next_element;
      }
      return root;
   }

   void
   merge(int first_element, int second_element)
   {
      int first_root = representative(first_element);
      int second_root = representative(second_element);
      if (first_root == second_root) {
         return;
      }

      if (rank_[first_root] < rank_[second_root]) {
         parent_[first_root] = second_root;
      } else if (rank_[second_root] < rank_[first_root]) {
         parent_[second_root] = first_root;
      } else {
         parent_[second_root] = first_root;
         ++rank_[first_root];
      }
   }

private:
   std::vector<int> parent_;
   std::vector<std::uint8_t> rank_;
};

/*
 * Construct the coarsest equivalence-class word satisfying every recorded
 * square constraint.  For a negative-sign constraint, the inserted letter is
 * in the second half of the completed square.  Its matching position in the
 * first half is insertion_gap - half_length; the two loops impose all other
 * equalities between the halves after accounting for the insertion shift.
 */
EncodedWord
build_required_letter_encoding(const ConstraintList& constraints, int word_length)
{
   DisjointSet equivalence_classes(word_length);

   for (const SquareConstraint& constraint : constraints) {
      const int matching_position = constraint.insertion_gap - constraint.half_length;

      for (int position = constraint.square_start; position < matching_position; ++position) {
         equivalence_classes.merge(position, position + constraint.half_length);
      }

      for (int position = matching_position + 1; position < constraint.square_start + constraint.half_length;
           ++position) {
         equivalence_classes.merge(position, position + constraint.half_length - 1);
      }
   }

   EncodedWord encoded_word(word_length);
   for (int position = 0; position < word_length; ++position) {
      encoded_word[position] = equivalence_classes.representative(position);
   }
   return encoded_word;
}

/*
 * Incrementally impose one constraint on an existing encoding.  Replacing an
 * entire class is simpler here than rebuilding the disjoint set, and is fast
 * for the short words considered by the lemma.
 */
void
merge_equivalence_classes(EncodedWord& encoded_word, int first_position, int second_position)
{
   const int retained_class = encoded_word[first_position];
   const int replaced_class = encoded_word[second_position];
   if (retained_class == replaced_class) {
      return;
   }

   for (int& equivalence_class : encoded_word) {
      if (equivalence_class == replaced_class) {
         equivalence_class = retained_class;
      }
   }
}

void
apply_constraint_to_encoding(EncodedWord& encoded_word, const SquareConstraint& constraint)
{
   const int matching_position = constraint.insertion_gap - constraint.half_length;

   for (int position = constraint.square_start; position < matching_position; ++position) {
      merge_equivalence_classes(encoded_word, position, position + constraint.half_length);
   }

   for (int position = matching_position + 1; position < constraint.square_start + constraint.half_length; ++position) {
      merge_equivalence_classes(encoded_word, position, position + constraint.half_length - 1);
   }
}

bool
constraints_have_square_free_witness(const ConstraintList& constraints, const EncodedWord& encoded_word)
{
   if (!is_square_free(encoded_word)) {
      return false;
   }

   for (const SquareConstraint& constraint : constraints) {
      const int inserted_class = encoded_word[constraint.insertion_gap - constraint.half_length];
      if (!insertion_preserves_minimality(encoded_word, constraint.insertion_gap, inserted_class,
                                          constraint.half_length, constraint.square_start)) {
         return false;
      }
   }

   return true;
}

// ---------------------------------------------------------------------------
// Enumeration of R_{S,k}
// ---------------------------------------------------------------------------

std::vector<RealisableTuple>
enumerate_realisable_tuples(const std::vector<int>& permitted_lengths, int tuple_length)
{
   std::vector<int> sorted_lengths = permitted_lengths;
   std::sort(sorted_lengths.begin(), sorted_lengths.end());

   if (sorted_lengths.empty()) {
      return {RealisableTuple(tuple_length)};
   }

   /*
    * Every constraint starting in the k-position window touches fewer than
    * 2*max(S) subsequent positions.  This finite word is therefore long
    * enough to test every equality and every possible competing square.
    */
   const int maximum_length = sorted_lengths.back();
   const int witness_word_length = tuple_length + 2 * maximum_length;

   std::vector<RealisableTuple> realisable_tuples;
   realisable_tuples.reserve(4096);
   realisable_tuples.emplace_back(tuple_length);

   /*
    * A tuple may have several witnesses, corresponding to different choices
    * of insertion gaps.  All witness constraint lists must be retained:
    * although they give the same tuple now, they need not admit the same
    * extensions later in the enumeration.
    */
   std::vector<std::vector<ConstraintList>> witnesses_by_tuple;
   witnesses_by_tuple.reserve(4096);
   witnesses_by_tuple.push_back({ConstraintList()});

   for (int half_length : sorted_lengths) {
      for (int square_start = 0; square_start < tuple_length; ++square_start) {
         /*
          * Only extend tuples that existed before this (start, length)
          * pair was considered.  Consequently each length occurs at most
          * once in each component, exactly as required for a set S_i.
          */
         const std::size_t previous_tuple_count = realisable_tuples.size();

         for (std::size_t tuple_index = 0; tuple_index < previous_tuple_count; ++tuple_index) {
            const RealisableTuple& current_tuple = realisable_tuples[tuple_index];
            const std::vector<ConstraintList>& current_witnesses = witnesses_by_tuple[tuple_index];

            std::vector<ConstraintList> extended_witnesses;
            extended_witnesses.reserve(current_witnesses.size() * static_cast<std::size_t>(half_length));

            for (const ConstraintList& current_constraints : current_witnesses) {
               const EncodedWord base_encoding
                     = build_required_letter_encoding(current_constraints, witness_word_length);
               ConstraintList candidate_constraints = current_constraints;
               candidate_constraints.reserve(candidate_constraints.size() + 1);

               // Negative sign means that the insertion gap lies in the
               // second half of the completed square.
               for (int offset_in_second_half = 0; offset_in_second_half < half_length; ++offset_in_second_half) {
                  const SquareConstraint candidate_constraint{square_start, half_length,
                                                              square_start + half_length + offset_in_second_half};
                  candidate_constraints.push_back(candidate_constraint);

                  EncodedWord candidate_encoding = base_encoding;
                  apply_constraint_to_encoding(candidate_encoding, candidate_constraint);

                  if (constraints_have_square_free_witness(candidate_constraints, candidate_encoding)) {
                     extended_witnesses.push_back(candidate_constraints);
                  }

                  candidate_constraints.pop_back();
               }
            }

            if (!extended_witnesses.empty()) {
               RealisableTuple extended_tuple = current_tuple;
               extended_tuple[square_start].push_back(half_length);

               realisable_tuples.push_back(std::move(extended_tuple));
               witnesses_by_tuple.push_back(std::move(extended_witnesses));
            }
         }
      }
   }

   return realisable_tuples;
}

// ---------------------------------------------------------------------------
// Construction of the weighted shift graph G_k(S)
// ---------------------------------------------------------------------------

struct WeightedEdge {
   int source;
   int target;
   int weight;
};

struct WeightedDigraph {
   int vertex_count = 0;
   std::vector<WeightedEdge> edges;
};

WeightedDigraph
build_weighted_shift_graph(const std::vector<RealisableTuple>& vertices)
{
   WeightedDigraph graph;
   graph.vertex_count = static_cast<int>(vertices.size());
   graph.edges.reserve(vertices.size() * 8);

   /*
    * There is an edge from (S_1,...,S_k) to (S'_1,...,S'_k) exactly when
    * (S_2,...,S_k)=(S'_1,...,S'_{k-1}).  Indexing targets by their prefix
    * avoids testing every ordered pair of vertices.
    */
   std::map<RealisableTuple, std::vector<int>> targets_by_prefix;
   for (std::size_t target_index = 0; target_index < vertices.size(); ++target_index) {
      const RealisableTuple& target = vertices[target_index];
      RealisableTuple target_prefix(target.begin(), target.end() - 1);
      targets_by_prefix[target_prefix].push_back(static_cast<int>(target_index));
   }

   for (std::size_t source_index = 0; source_index < vertices.size(); ++source_index) {
      const RealisableTuple& source = vertices[source_index];
      const RealisableTuple shifted_source(source.begin() + 1, source.end());

      const auto matching_targets = targets_by_prefix.find(shifted_source);
      if (matching_targets == targets_by_prefix.end()) {
         continue;
      }

      for (int target_index : matching_targets->second) {
         // By definition, the edge weight is |S'_k|.
         graph.edges.push_back(
               {static_cast<int>(source_index), target_index, static_cast<int>(vertices[target_index].back().size())});
      }
   }

   return graph;
}

// ---------------------------------------------------------------------------
// Exact, tie-safe Howard maximum-mean-cycle algorithm
// ---------------------------------------------------------------------------

struct AdjacencyEntry {
   int target;
   int weight;
   int graph_edge_index;
};

struct MaximumMeanCycle {
   long long total_weight = 0;
   int edge_count = 0;
   std::vector<int> vertices;
   std::vector<int> edge_weights;
   std::vector<int> graph_edge_indices;

   /*
    * If the candidate mean is total_weight/edge_count, these integer
    * potentials satisfy
    *
    *   edge_count*weight(u,v) - total_weight + potential[v]
    *       <= potential[u]
    *
    * for every edge (u,v).  Summing this inequality around any cycle proves
    * that its mean is at most the candidate mean.
    */
   std::vector<long long> potential;
};

/*
 * All policy comparisons below use scaled integers rather than floating
 * point.  A potential is bounded in magnitude by 2*|V|^2*max_edge_weight.
 * Reject inputs for which that conservative bound might overflow long long.
 */
void
check_exact_arithmetic_bounds(const WeightedDigraph& graph)
{
   long long maximum_edge_weight = 0;
   for (const WeightedEdge& edge : graph.edges) {
      if (edge.weight < 0) {
         throw std::invalid_argument("maximum-mean-cycle solver requires nonnegative edge weights");
      }
      maximum_edge_weight = std::max(maximum_edge_weight, static_cast<long long>(edge.weight));
   }

   if (graph.vertex_count <= 0 || maximum_edge_weight == 0) {
      return;
   }

   const long long vertex_count = graph.vertex_count;
   const long long safe_limit = std::numeric_limits<long long>::max() / 4;
   if (vertex_count > safe_limit / maximum_edge_weight) {
      throw std::overflow_error("graph is too large for exact 64-bit policy arithmetic");
   }
   const long long vertex_weight_product = vertex_count * maximum_edge_weight;
   if (vertex_count > safe_limit / (2 * vertex_weight_product)) {
      throw std::overflow_error("graph is too large for exact 64-bit policy arithmetic");
   }
}

MaximumMeanCycle
find_maximum_mean_cycle(const WeightedDigraph& graph)
{
   const int vertex_count = graph.vertex_count;

   if (vertex_count == 0) {
      return {};
   }
   check_exact_arithmetic_bounds(graph);
   if (graph.edges.size() > static_cast<std::size_t>(std::numeric_limits<int>::max())) {
      throw std::overflow_error("graph has too many edges for 32-bit indices");
   }

   std::vector<int> outgoing_edge_counts(vertex_count, 0);
   for (int edge_index = 0; edge_index < static_cast<int>(graph.edges.size()); ++edge_index) {
      const WeightedEdge& edge = graph.edges[edge_index];
      if (edge.source < 0 || edge.source >= vertex_count || edge.target < 0 || edge.target >= vertex_count) {
         throw std::invalid_argument("edge endpoint is outside the graph");
      }
      ++outgoing_edge_counts[edge.source];
   }

   std::vector<std::vector<AdjacencyEntry>> adjacency(vertex_count);
   for (int vertex = 0; vertex < vertex_count; ++vertex) {
      adjacency[vertex].reserve(outgoing_edge_counts[vertex]);
   }
   for (int edge_index = 0; edge_index < static_cast<int>(graph.edges.size()); ++edge_index) {
      const WeightedEdge& edge = graph.edges[edge_index];
      adjacency[edge.source].push_back({edge.target, edge.weight, edge_index});
   }

   /*
    * A policy selects one outgoing edge at every non-sink vertex.  Starting
    * with a maximum-weight outgoing edge usually reduces the number of policy
    * improvements required.
    */
   std::vector<int> selected_edge_index(vertex_count, -1);
   for (int vertex = 0; vertex < vertex_count; ++vertex) {
      if (adjacency[vertex].empty()) {
         continue;
      }

      int heaviest_edge_index = 0;
      for (int edge_index = 1; edge_index < static_cast<int>(adjacency[vertex].size()); ++edge_index) {
         if (adjacency[vertex][edge_index].weight > adjacency[vertex][heaviest_edge_index].weight) {
            heaviest_edge_index = edge_index;
         }
      }
      selected_edge_index[vertex] = heaviest_edge_index;
   }

   std::vector<int> policy_successor(vertex_count, -1);
   std::vector<int> policy_edge_weight(vertex_count, 0);
   std::vector<int> policy_graph_edge_index(vertex_count, -1);

   /*
    * The reverse policy graph is represented by three flat arrays.  This
    * avoids a large number of small allocations inside the policy loop.
    */
   std::vector<int> reverse_head(vertex_count, -1);
   std::vector<int> reverse_predecessor(vertex_count, -1);
   std::vector<int> reverse_next(vertex_count, -1);

   // Scratch storage used to locate all cycles of the current policy graph.
   std::vector<int> visit_state(vertex_count, 0);
   std::vector<int> traversal_root(vertex_count, -1);
   std::vector<int> position_in_path(vertex_count, -1);
   std::vector<int> current_path;
   current_path.reserve(vertex_count);
   std::vector<int> best_cycle_vertices;

   // Scaled integer potentials are used to compare policy edges exactly.
   std::vector<long long> potential(vertex_count, 0);
   std::vector<bool> has_potential(vertex_count, false);
   std::vector<bool> is_on_best_cycle(vertex_count, false);
   std::deque<int> propagation_queue;

   while (true) {
      // Materialise the directed pseudoforest induced by the current policy.
      std::fill(reverse_head.begin(), reverse_head.end(), -1);
      int reverse_edge_count = 0;
      for (int source = 0; source < vertex_count; ++source) {
         const int edge_index = selected_edge_index[source];
         if (edge_index < 0) {
            policy_successor[source] = -1;
            policy_edge_weight[source] = 0;
            policy_graph_edge_index[source] = -1;
            continue;
         }

         const AdjacencyEntry selected_edge = adjacency[source][edge_index];
         policy_successor[source] = selected_edge.target;
         policy_edge_weight[source] = selected_edge.weight;
         policy_graph_edge_index[source] = selected_edge.graph_edge_index;

         if (selected_edge.target >= 0 && selected_edge.target < vertex_count) {
            reverse_predecessor[reverse_edge_count] = source;
            reverse_next[reverse_edge_count] = reverse_head[selected_edge.target];
            reverse_head[selected_edge.target] = reverse_edge_count;
            ++reverse_edge_count;
         }
      }

      // Find the greatest-mean cycle in the current policy graph.
      std::fill(visit_state.begin(), visit_state.end(), 0);
      best_cycle_vertices.clear();
      long long best_policy_cycle_weight = 0;
      int best_policy_cycle_length = 0;

      for (int start_vertex = 0; start_vertex < vertex_count; ++start_vertex) {
         if (visit_state[start_vertex] != 0 || policy_successor[start_vertex] == -1) {
            continue;
         }

         current_path.clear();
         int vertex = start_vertex;
         while (vertex != -1 && visit_state[vertex] == 0) {
            visit_state[vertex] = 1;
            traversal_root[vertex] = start_vertex;
            position_in_path[vertex] = static_cast<int>(current_path.size());
            current_path.push_back(vertex);
            vertex = policy_successor[vertex];
         }

         const bool closed_within_current_path
               = vertex != -1 && visit_state[vertex] == 1 && traversal_root[vertex] == start_vertex;
         if (closed_within_current_path) {
            const int cycle_start_position = position_in_path[vertex];
            long long cycle_weight = 0;
            for (int path_position = cycle_start_position; path_position < static_cast<int>(current_path.size());
                 ++path_position) {
               cycle_weight += policy_edge_weight[current_path[path_position]];
            }

            const int cycle_length = static_cast<int>(current_path.size()) - cycle_start_position;
            const bool is_first_cycle = best_policy_cycle_length == 0;
            const bool has_larger_mean = !is_first_cycle
                                         && cycle_weight * best_policy_cycle_length
                                                  > best_policy_cycle_weight * static_cast<long long>(cycle_length);
            if (is_first_cycle || has_larger_mean) {
               best_policy_cycle_weight = cycle_weight;
               best_policy_cycle_length = cycle_length;
               best_cycle_vertices.assign(current_path.begin() + cycle_start_position, current_path.end());
            }
         }

         for (int path_vertex : current_path) {
            visit_state[path_vertex] = 2;
         }
      }

      if (best_cycle_vertices.empty()) {
         return {};
      }

      /*
       * Set scaled potentials on the best policy cycle so that
       *
       *   potential[u]
       *       = cycle_length*weight(u,v) - cycle_weight + potential[v].
       *
       * Then propagate the same equality backwards through its policy tree.
       */
      std::fill(has_potential.begin(), has_potential.end(), false);
      std::fill(is_on_best_cycle.begin(), is_on_best_cycle.end(), false);
      propagation_queue.clear();
      potential[best_cycle_vertices.front()] = 0;
      has_potential[best_cycle_vertices.front()] = true;
      is_on_best_cycle[best_cycle_vertices.front()] = true;

      for (int cycle_position = 1; cycle_position < static_cast<int>(best_cycle_vertices.size()); ++cycle_position) {
         const int previous_vertex = best_cycle_vertices[cycle_position - 1];
         const int current_vertex = best_cycle_vertices[cycle_position];
         potential[current_vertex]
               = potential[previous_vertex]
                 - static_cast<long long>(best_policy_cycle_length) * policy_edge_weight[previous_vertex]
                 + best_policy_cycle_weight;
         has_potential[current_vertex] = true;
         is_on_best_cycle[current_vertex] = true;
      }

      for (int cycle_vertex : best_cycle_vertices) {
         propagation_queue.push_back(cycle_vertex);
      }

      while (!propagation_queue.empty()) {
         const int target = propagation_queue.front();
         propagation_queue.pop_front();

         for (int reverse_edge = reverse_head[target]; reverse_edge != -1; reverse_edge = reverse_next[reverse_edge]) {
            const int predecessor = reverse_predecessor[reverse_edge];
            if (is_on_best_cycle[predecessor] || has_potential[predecessor]) {
               continue;
            }

            potential[predecessor] = static_cast<long long>(best_policy_cycle_length) * policy_edge_weight[predecessor]
                                     - best_policy_cycle_weight + potential[policy_successor[predecessor]];
            has_potential[predecessor] = true;
            propagation_queue.push_back(predecessor);
         }
      }

      /*
       * Vertices outside the selected cycle's policy basin are first linked
       * into that basin.  At vertices already in the basin, change an edge
       * only for a strict improvement.  In particular, retaining the current
       * edge on equality prevents oscillation between distinct cycles of the
       * same mean.
       */
      bool policy_changed = false;
      for (int source = 0; source < vertex_count; ++source) {
         if (adjacency[source].empty()) {
            continue;
         }

         const int current_edge_index = selected_edge_index[source];
         int best_edge_index = -1;
         long long best_reduced_weight = 0;

         for (int edge_index = 0; edge_index < static_cast<int>(adjacency[source].size()); ++edge_index) {
            const AdjacencyEntry& candidate_edge = adjacency[source][edge_index];
            if (!has_potential[candidate_edge.target]) {
               continue;
            }

            const long long reduced_weight = static_cast<long long>(best_policy_cycle_length) * candidate_edge.weight
                                             - best_policy_cycle_weight + potential[candidate_edge.target];
            if (best_edge_index == -1 || reduced_weight > best_reduced_weight) {
               best_reduced_weight = reduced_weight;
               best_edge_index = edge_index;
            }
         }

         if (!has_potential[source] && best_edge_index != -1 && best_edge_index != current_edge_index) {
            // Grow the selected policy basin, even if this first link is not
            // a strict reduced-weight improvement.
            selected_edge_index[source] = best_edge_index;
            policy_changed = true;
         } else if (has_potential[source] && best_edge_index != -1 && best_reduced_weight > potential[source]) {
            selected_edge_index[source] = best_edge_index;
            policy_changed = true;
         }
      }

      if (!policy_changed) {
         if (!std::all_of(has_potential.begin(), has_potential.end(), [](bool value) { return value; })) {
            throw std::logic_error("policy graph does not reach the selected cycle; input must be strongly connected");
         }

         MaximumMeanCycle result;
         result.total_weight = best_policy_cycle_weight;
         result.edge_count = best_policy_cycle_length;
         result.vertices = best_cycle_vertices;
         result.potential = potential;
         for (int cycle_vertex : best_cycle_vertices) {
            result.edge_weights.push_back(policy_edge_weight[cycle_vertex]);
            result.graph_edge_indices.push_back(policy_graph_edge_index[cycle_vertex]);
         }
         return result;
      }
   }
}

/*
 * Verify both sides of the optimum claim using integer arithmetic:
 *
 *  - the recorded edges form a cycle of the claimed mean (lower bound), and
 *  - the potential inequality holds for every graph edge (upper bound).
 */
bool
verify_maximum_mean_cycle_certificate(const WeightedDigraph& graph, const MaximumMeanCycle& candidate)
{
   if (candidate.edge_count <= 0 || candidate.vertices.size() != static_cast<std::size_t>(candidate.edge_count)
       || candidate.edge_weights.size() != candidate.vertices.size()
       || candidate.graph_edge_indices.size() != candidate.vertices.size()
       || candidate.potential.size() != static_cast<std::size_t>(graph.vertex_count)) {
      return false;
   }

   long long witnessed_cycle_weight = 0;
   for (int cycle_position = 0; cycle_position < candidate.edge_count; ++cycle_position) {
      const int source = candidate.vertices[cycle_position];
      const int target = candidate.vertices[(cycle_position + 1) % candidate.edge_count];
      const int weight = candidate.edge_weights[cycle_position];
      const int graph_edge_index = candidate.graph_edge_indices[cycle_position];

      if (graph_edge_index < 0 || graph_edge_index >= static_cast<int>(graph.edges.size())) {
         return false;
      }
      const WeightedEdge& edge = graph.edges[graph_edge_index];
      if (edge.source != source || edge.target != target || edge.weight != weight) {
         return false;
      }
      witnessed_cycle_weight += weight;
   }
   if (witnessed_cycle_weight != candidate.total_weight) {
      return false;
   }

   for (const WeightedEdge& edge : graph.edges) {
      const long long transformed_edge_weight
            = static_cast<long long>(candidate.edge_count) * edge.weight - candidate.total_weight;
      if (transformed_edge_weight + candidate.potential[edge.target] > candidate.potential[edge.source]) {
         return false;
      }
   }

   return true;
}

int
parse_integer_argument(const char* text, const std::string& argument_name)
{
   std::size_t parsed_character_count = 0;
   const long parsed_value = std::stol(text, &parsed_character_count);
   if (parsed_character_count != std::string(text).size() || parsed_value < std::numeric_limits<int>::min()
       || parsed_value > std::numeric_limits<int>::max()) {
      throw std::invalid_argument(argument_name + " must be an integer in the range of int");
   }
   return static_cast<int>(parsed_value);
}

}  // namespace

int
main(int argument_count, char** arguments)
{
   if (argument_count != 4) {
      std::cerr << "Usage: " << arguments[0] << " tuple_length range_start range_end_exclusive\n";
      return 1;
   }

   int tuple_length;
   int range_start;
   int range_end_exclusive;
   try {
      tuple_length = parse_integer_argument(arguments[1], "tuple_length");
      range_start = parse_integer_argument(arguments[2], "range_start");
      range_end_exclusive = parse_integer_argument(arguments[3], "range_end_exclusive");
   } catch (const std::exception& error) {
      std::cerr << "Invalid arguments: " << error.what() << '\n';
      return 1;
   }

   if (tuple_length <= 0 || range_start < 2 || range_end_exclusive <= range_start) {
      std::cerr << "Invalid arguments: require tuple_length > 0 and "
                << "2 <= range_start < range_end_exclusive.\n";
      return 1;
   }

   // Avoid signed overflow when the finite witness-word length is computed.
   const long long largest_witness_word_length
         = static_cast<long long>(tuple_length) + 2LL * (range_end_exclusive - 1LL);
   if (largest_witness_word_length > std::numeric_limits<int>::max()) {
      std::cerr << "Invalid arguments: requested word length is too large.\n";
      return 1;
   }

   const auto computation_start = std::chrono::steady_clock::now();

   std::vector<int> permitted_lengths;
   permitted_lengths.reserve(static_cast<std::size_t>(static_cast<long long>(range_end_exclusive) - range_start));
   for (int length = range_start; length < range_end_exclusive; ++length) {
      permitted_lengths.push_back(length);
   }

   const std::vector<RealisableTuple> vertices = enumerate_realisable_tuples(permitted_lengths, tuple_length);
   std::cout << "Vertex set size: " << vertices.size() << '\n';

   const WeightedDigraph graph = build_weighted_shift_graph(vertices);
   std::cout << "Vertices: " << graph.vertex_count << '\n';
   std::cout << "Edges: " << graph.edges.size() << '\n';

   const MaximumMeanCycle maximum_mean_cycle = find_maximum_mean_cycle(graph);
   if (maximum_mean_cycle.edge_count == 0) {
      std::cout << "Maximum mean cycle: no directed cycle\n";
   } else {
      if (!verify_maximum_mean_cycle_certificate(graph, maximum_mean_cycle)) {
         std::cerr << "Internal error: exact maximum-mean-cycle certificate failed verification.\n";
         return 2;
      }

      const long long common_divisor
            = std::gcd(maximum_mean_cycle.total_weight, static_cast<long long>(maximum_mean_cycle.edge_count));
      const long long reduced_numerator = maximum_mean_cycle.total_weight / common_divisor;
      const long long reduced_denominator = maximum_mean_cycle.edge_count / common_divisor;
      const long double decimal_mean
            = static_cast<long double>(maximum_mean_cycle.total_weight) / maximum_mean_cycle.edge_count;

      std::cout << "Maximum mean cycle: " << reduced_numerator << '/' << reduced_denominator << " ("
                << std::setprecision(15) << decimal_mean << ")\n";
      std::cout << "Exact optimality certificate: verified\n";
   }

   const auto computation_end = std::chrono::steady_clock::now();
   const std::chrono::duration<double> elapsed_time = computation_end - computation_start;
   std::cout << "Total runtime (s): " << elapsed_time.count() << '\n';

   return 0;
}
