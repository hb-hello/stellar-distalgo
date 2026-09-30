import unittest

import quorum
from quorum_intersection import QuorumIntersectionChecker


## builds one QuorumChecker2 seeded with v's own D, then learns every other node's D into
## the same graph via add() - mirrors how scp.da incrementally learns peers' D's
def build_checker(v, node_specs):
  qc = quorum.QuorumChecker2(v, node_specs[v])
  for v2, D2 in node_specs.items():
    if v2 != v:
      qc.add(v2, D2)
  return qc


## Cases adapted from stellar-core's examples/QuorumIntersectionTests.cpp
class TestQuorumIntersection(unittest.TestCase):
  def test_basic_4node_intersects(self):
    qc = build_checker(
      "A",
      {
        "A": (2, {"B", "C", "D"}),
        "B": (2, {"A", "C", "D"}),
        "C": (2, {"A", "B", "D"}),
        "D": (2, {"A", "B", "C"}),
      },
    )
    self.assertTrue(
      QuorumIntersectionChecker(qc.quorum_graph).has_quorum_intersection()
    )
    self.assertTrue(qc.quorum({"A", "B", "C"}))
    self.assertTrue(qc.v_blocking({"B", "C"}))
    self.assertFalse(qc.v_blocking({"B"}))

  def test_basic_4node_non_intersecting(self):
    qc = build_checker(
      "A",
      {
        "A": (1, {"B", "C", "D"}),
        "B": (1, {"A", "C", "D"}),
        "C": (1, {"A", "B", "D"}),
        "D": (1, {"A", "B", "C"}),
      },
    )
    self.assertFalse(
      QuorumIntersectionChecker(qc.quorum_graph).has_quorum_intersection()
    )
    self.assertTrue(qc.v_blocking({"B", "C", "D"}))
    self.assertFalse(qc.v_blocking({"B", "C"}))

  ## quorum no-quorum threshold exceeds degree: a "ghost" validator referenced by others'
  ## quorum sets but itself absent, so no node can ever reach its threshold - the FBAS admits
  ## no quorum at all (NO_QUORUM, distinct from UNSAT/"enjoys intersection")
  def test_no_quorum_when_threshold_exceeds_reachable_degree(self):
    qc = build_checker(
      "A",
      {
        "A": (3, {"A", "B", "Ghost"}),
        "B": (3, {"A", "B", "Ghost"}),
        "C": (3, {"C", "D", "Ghost"}),
        "D": (3, {"C", "D", "Ghost"}),
      },
    )
    self.assertTrue(
      QuorumIntersectionChecker(qc.quorum_graph).has_quorum_intersection()
    )
    self.assertFalse(qc.quorum({"A", "B", "C", "D", "Ghost"}))
    ## Ghost can never be *in* a quorum, but it can still block one: threshold 3-of-3
    ## means excluding any single member (even the unreachable Ghost) breaks the slice
    self.assertTrue(qc.v_blocking({"Ghost"}))
    self.assertFalse(qc.v_blocking(set()))

  def test_6node_with_subquorums_intersects(self):
    def qs(*names):
      return (2, frozenset(names))

    qsABC, qsABD, qsABE, qsABF = (
      qs("A", "B", "C"),
      qs("A", "B", "D"),
      qs("A", "B", "E"),
      qs("A", "B", "F"),
    )
    qsACD, qsACE, qsACF = (
      qs("A", "C", "D"),
      qs("A", "C", "E"),
      qs("A", "C", "F"),
    )
    qsBDC, qsBDE, qsCDE = (
      qs("B", "D", "C"),
      qs("B", "D", "E"),
      qs("C", "D", "E"),
    )

    qc = build_checker(
      "A",
      {
        "A": (2, frozenset({qsBDC, qsBDE, qsCDE})),
        "B": (2, frozenset({qsACD, qsACE, qsACF})),
        "C": (2, frozenset({qsABD, qsABE, qsABF})),
        "D": (2, frozenset({qsABC, qsABE, qsABF})),
        "E": (2, frozenset({qsABC, qsABD, qsABF})),
        "F": (2, frozenset({qsABC, qsABD, qsABE})),
      },
    )
    self.assertTrue(
      QuorumIntersectionChecker(qc.quorum_graph).has_quorum_intersection()
    )
    ## blocking a nested group: {B,D} blocks 2 of A's 3 inner sets (qsBDC, qsBDE),
    ## meeting A's own 2-of-3 blocking threshold
    self.assertTrue(qc.v_blocking({"B", "D"}))
    self.assertFalse(qc.v_blocking({"B"}))

  def test_plausible_non_intersection(self):
    lobstr = (1, frozenset({"LOBSTR1", "LOBSTR2"}))
    coinqvest = (1, frozenset({"COINQVEST1", "COINQVEST2"}))
    sdf_1of3 = (1, frozenset({"SDF1", "SDF2", "SDF3"}))
    satoshi_2of3 = (2, frozenset({"Satoshi1", "Satoshi2", "Satoshi3"}))

    D_sdf = (3, frozenset({"SDF1", "SDF2", "SDF3", lobstr, satoshi_2of3}))
    D_satoshi = (
      4,
      frozenset(
        {
          "Satoshi1",
          "Satoshi2",
          "Satoshi3",
          sdf_1of3,
          lobstr,
          coinqvest,
        }
      ),
    )
    D_lobstr = (
      5,
      frozenset({"SDF1", "SDF2", "SDF3", "Satoshi1", "Satoshi2", "Satoshi3"}),
    )
    D_coinqvest = (
      3,
      frozenset({"COINQVEST1", "COINQVEST2", sdf_1of3, satoshi_2of3, lobstr}),
    )

    qc = build_checker(
      "SDF1",
      {
        "SDF1": D_sdf,
        "SDF2": D_sdf,
        "SDF3": D_sdf,
        "Satoshi1": D_satoshi,
        "Satoshi2": D_satoshi,
        "Satoshi3": D_satoshi,
        "LOBSTR1": D_lobstr,
        "LOBSTR2": D_lobstr,
        "COINQVEST1": D_coinqvest,
        "COINQVEST2": D_coinqvest,
      },
    )
    self.assertFalse(
      QuorumIntersectionChecker(qc.quorum_graph).has_quorum_intersection()
    )

  ## quorum intersection 8-org core-and-periphery dangling: "looks kinda strong" but still
  ## capable of splitting in half, since the core's 5/7 threshold can be satisfied by its own
  ## 3 nodes + 1 other core org + 1 periphery org, without a majority of the core orgs
  def test_8org_core_and_periphery_dangling_non_intersecting(self):
    org0, org1 = (
      ["org0.n0", "org0.n1", "org0.n2"],
      ["org1.n0", "org1.n1", "org1.n2"],
    )
    org2, org3 = (
      ["org2.n0", "org2.n1", "org2.n2"],
      ["org3.n0", "org3.n1", "org3.n2"],
    )
    org4, org5, org6, org7 = (
      ["org4.n0", "org4.n1"],
      ["org5.n0", "org5.n1"],
      ["org6.n0", "org6.n1"],
      ["org7.n0", "org7.n1"],
    )

    ## roundUpPct(_, 51) == 2 for both org sizes here
    def majority(org):
      return (2, frozenset(org))

    inner0, inner1, inner2, inner3 = (
      majority(org0),
      majority(org1),
      majority(org2),
      majority(org3),
    )
    inner4, inner5, inner6, inner7 = (
      majority(org4),
      majority(org5),
      majority(org6),
      majority(org7),
    )

    node_specs = {}
    for org, peer_inners, periphery_inner in [
      (org0, (inner1, inner2, inner3), inner4),
      (org1, (inner0, inner2, inner3), inner5),
      (org2, (inner0, inner1, inner3), inner6),
      (org3, (inner0, inner1, inner2), inner7),
    ]:
      D = (5, frozenset(set(org) | set(peer_inners) | {periphery_inner}))
      for v in org:
        node_specs[v] = D

    for org, core_inner in [
      (org4, inner0),
      (org5, inner1),
      (org6, inner2),
      (org7, inner3),
    ]:
      D = (3, frozenset(set(org) | {core_inner}))
      for v in org:
        node_specs[v] = D

    qc = build_checker("org0.n0", node_specs)
    self.assertFalse(
      QuorumIntersectionChecker(qc.quorum_graph).has_quorum_intersection()
    )


if __name__ == "__main__":
  unittest.main()
