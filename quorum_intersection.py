# type: ignore

from ortools.sat.python import cp_model


## Checks whether an FBAS enjoys quorum intersection by searching for a counterexample:
## two disjoint, nonempty quorums. UNSAT means every pair of quorums intersects.
## Takes the same quorum_graph shape as QuorumChecker2 (quorum.py): node -> top group id,
## group id -> (threshold, children), discriminated by the 'grp:' prefix.
class QuorumIntersectionChecker:
  def __init__(self, quorum_graph: dict):
    self.quorum_graph = quorum_graph
    self.validators = sorted(self._all_leaves(quorum_graph))

  ## every leaf ever mentioned, whether it has its own D (a quorum_graph key) or is only
  ## referenced as a child inside some other node's group - e.g. an absent/"ghost" validator
  @staticmethod
  def _all_leaves(quorum_graph):
    leaves = set()
    for vertex, value in quorum_graph.items():
      if vertex.startswith("grp:"):
        _, children = value
        leaves.update(c for c in children if not c.startswith("grp:"))
      else:
        leaves.add(vertex)
    return leaves

  ## adds one membership assignment (a candidate quorum) to the model, tagged by suffix
  ## so the two candidates get distinct variables. Returns {validator: BoolVar}.
  def _add_candidate(self, model, suffix):
    x = {v: model.new_bool_var(f"{v}{suffix}") for v in self.validators}
    for v in self.validators:
      if self.quorum_graph.get(v) is None:
        ## no D of its own - mirrors check_threshold(None, ...) == False in quorum.py,
        ## so it can never actually belong to any quorum
        model.add(x[v] == 0)
    sat = {}  ## group id -> reified BoolVar, memoized like QuorumChecker2.check_threshold

    ## sat_var(v)=1 only *forces* enough children to hold - we never need the converse,
    ## since v is only ever used on the right side of an implication (see below)
    def sat_var(vertex):
      if not vertex.startswith("grp:"):
        return x[vertex]
      if vertex in sat:
        return sat[vertex]
      threshold, children = self.quorum_graph[vertex]
      terms = [sat_var(c) for c in children]
      v = model.new_bool_var(f"{vertex}{suffix}")
      model.add(sum(terms) >= threshold).only_enforce_if(v)
      sat[vertex] = v
      return v

    for name in self.validators:
      top = self.quorum_graph.get(name)
      if top is not None:
        model.add_implication(x[name], sat_var(top))
    model.add(sum(x.values()) >= 1)
    return x

  ## returns (U1, U2), two disjoint nonempty quorums, if the FBAS fails intersection;
  ## else None (quorum intersection holds for every pair of quorums)
  def find_counterexample(self):
    model = cp_model.CpModel()
    x1 = self._add_candidate(model, "_1")
    x2 = self._add_candidate(model, "_2")
    for v in self.validators:
      model.add(x1[v] + x2[v] <= 1)

    solver = cp_model.CpSolver()
    status = solver.solve(model)
    if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
      return None
    U1 = {v for v in self.validators if solver.value(x1[v])}
    U2 = {v for v in self.validators if solver.value(x2[v])}
    return U1, U2

  def has_quorum_intersection(self) -> bool:
    return self.find_counterexample() is None


if __name__ == "__main__":
  import quorum

  ## builds one QuorumChecker2 seeded with v's own D, then learns every other node's D
  ## into the same graph via add() - mirrors how scp.da incrementally learns peers' D's
  def build_graph(node_specs):
    v0 = next(iter(node_specs))
    qc = quorum.QuorumChecker2(v0, node_specs[v0])
    for v, D in node_specs.items():
      if v != v0:
        qc.add(v, D)
    return qc.quorum_graph

  ## safe: A and B share a 2-of-3 majority requirement over the SAME core {A,B,C} - any two
  ## majority subsets of a 3-set must overlap, so intersection holds by construction
  safe_graph = build_graph(
    {
      "A": (2, {"A", "B", "C"}),
      "B": (2, {"A", "B", "C"}),
      "C": (2, {"A", "B", "C"}),
    }
  )
  safe = QuorumIntersectionChecker(safe_graph)
  print("safe graph has_quorum_intersection:", safe.has_quorum_intersection())

  ## unsafe: A and B's D's both reference X, but each can route around it via Y/Z instead -
  ## {A,Y} and {B,Z} are disjoint quorums (see conversation for the worked argument)
  unsafe_graph = build_graph(
    {
      "A": (2, {"A", "X", "Y"}),
      "B": (2, {"B", "X", "Z"}),
      "X": (1, {"X"}),
      "Y": (1, {"Y"}),
      "Z": (1, {"Z"}),
    }
  )
  unsafe = QuorumIntersectionChecker(unsafe_graph)
  print(
    "unsafe graph has_quorum_intersection:", unsafe.has_quorum_intersection()
  )
  print("counterexample:", unsafe.find_counterexample())
