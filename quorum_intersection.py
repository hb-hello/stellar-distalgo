# type: ignore

from ortools.sat.python import cp_model


def is_nested(m):
  return isinstance(m, tuple) and len(m) == 2

def freeze(D):
  t, members = D
  return (t, frozenset(freeze(m) if is_nested(m) else m for m in members))

def leaves(D):
  return set().union(*(leaves(m) if is_nested(m) else {m} for m in D[1]))

## Checks whether an FBAS enjoys quorum intersection by searching for a counterexample:
## two disjoint, nonempty quorums. UNSAT means every pair of quorums intersects.
## Takes Ds: node -> D, the same (threshold, members) trees quorum.da uses.
class QuorumIntersectionChecker:
  def __init__(self, Ds: dict):
    self.Ds = {v: freeze(D) for v, D in Ds.items()}
    self.validators = sorted(set(self.Ds).union(*(leaves(D) for D in self.Ds.values())), key=str)

  ## adds one membership assignment (a candidate quorum) to the model, tagged by suffix
  ## so the two candidates get distinct variables. Returns {validator: BoolVar}.
  def _add_candidate(self, model, suffix):
    x = {v: model.new_bool_var(f"{v}{suffix}") for v in self.validators}
    for v in self.validators:
      if v not in self.Ds:
        ## no D of its own, so it can never actually belong to any quorum
        model.add(x[v] == 0)
    sat = {}  ## nested D -> reified BoolVar, so a group shared by many nodes' Ds gets one variable

    ## sat_var(m)=1 only *forces* enough members to hold - we never need the converse,
    ## since it's only ever used on the right side of an implication (see below)
    def sat_var(m):
      if not is_nested(m):
        return x[m]
      if m not in sat:
        t, members = m
        sat[m] = model.new_bool_var(f"g{len(sat)}{suffix}")
        model.add(sum(sat_var(c) for c in members) >= t).only_enforce_if(sat[m])
      return sat[m]

    for v, D in self.Ds.items():
      model.add_implication(x[v], sat_var(D))
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
