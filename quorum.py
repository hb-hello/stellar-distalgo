import hashlib

## quorum_graph holds two kinds of entries: node -> its top group id, and
## group id -> (threshold, children). Group ids are content-addressed
## ('grp:' + hash of (threshold, sorted(children))) so identical subtrees
## dedup onto one entry, and double as the leaf/group discriminator: any
## vertex not starting with 'grp:' is a plain validator name (a leaf).
## quorum_graph is shared and grows as a node learns peers' D's (dict.update).


def add_group(quorum_graph: dict, threshold: int, children_ids: set) -> str:
  children_ids = frozenset(children_ids)
  group_id = (
    "grp:"
    + hashlib.sha256(
      f"{threshold}:{','.join(sorted(children_ids))}".encode()
    ).hexdigest()[:16]
  )
  quorum_graph.setdefault(group_id, (threshold, children_ids))
  return group_id


def build_group(quorum_graph: dict, D: tuple) -> str:
  threshold, members = D
  children_ids = {
    build_group(quorum_graph, m)
    if isinstance(m, tuple) and len(m) == 2
    else str(m)
    for m in members
  }
  return add_group(quorum_graph, threshold, children_ids)


## e_k(counts) - sum over every k-subset of counts of the subset's product.
## nCr(len(counts), k) is the special case where every count is 1.
def _symmetric_sum(counts, k) -> int:
  dp = [1] + [0] * k
  for c in counts:
    for j in range(k, 0, -1):
      dp[j] += dp[j - 1] * c
  return dp[k]


class QuorumChecker2:
  ## assumes quorum_graph is acyclic - not checked here
  ## v is this checker's own node id; D is v's own D, used to seed quorum_graph
  def __init__(self, v, D):
    self.v = v
    self.quorum_graph = {}
    self.num_slices, self._slices_with = 0, {}
    self.add(v, D)

  ## insert/replace node v's D into quorum_graph (rebuilding its subtree via build_group),
  ## then - only if v is self.v - refresh the cached slice counts used by weight(), since
  ## that's the one node whose counts we cache rather than re-walk on every call. Used both
  ## to seed self.v's own D in __init__ and to learn peers' D's into the same graph later.
  def add(self, v, D):
    self.quorum_graph[v] = build_group(self.quorum_graph, D)
    if v == self.v:
      self.num_slices, self._slices_with = self._compute_slices(
        self.quorum_graph.get(self.v)
      )

  ## single bottom-up pass computing, per vertex, both count_slices(vertex) and
  ## {leaf: count_slices_with(leaf, vertex)} together, since they share the same recursion
  def _compute_slices(self, vertex, counts=None, withs=None):
    if vertex is None:
      return 0, {}
    if counts is None:
      counts = {}
    if withs is None:
      withs = {}
    if vertex in counts:
      return counts[vertex], withs[vertex]
    if not vertex.startswith("grp:"):
      count, with_ = 1, {vertex: 1}
    else:
      threshold, children = self.quorum_graph[vertex]
      child_counts, child_withs = zip(
        *(self._compute_slices(c, counts, withs) for c in children)
      )
      count = _symmetric_sum(child_counts, threshold)
      leaves = set().union(*child_withs)
      with_ = {
        leaf: count
        - _symmetric_sum(
          [c - w.get(leaf, 0) for c, w in zip(child_counts, child_withs)],
          threshold,
        )
        for leaf in leaves
      }
    counts[vertex], withs[vertex] = count, with_
    return count, with_

  def quorum(self, U) -> bool:
    nodes = set(U)
    while self.v in nodes:
      memo = {}  ## shared across every n checked this pass - nodes is fixed for the whole pass
      to_remove = {
        n
        for n in nodes
        if not self.check_threshold(
          self.quorum_graph.get(n),
          self.quorum_graph,
          nodes,
          blocking=False,
          memo=memo,
        )
      }
      if not to_remove:
        break
      nodes -= to_remove
    return self.v in nodes

  def v_blocking(self, selected_validators: set) -> bool:
    return self.check_threshold(
      self.quorum_graph.get(self.v),
      self.quorum_graph,
      selected_validators,
      blocking=True,
    )

  # weight(v, v2) = |{q | q ∈ Q(v) & v2 ∈ q}| / |Q(v)|
  # The function weight (v, v2) returns the fraction of slices in Q(v) containing v2
  def weight(self, v2) -> float:
    return (
      self._slices_with.get(v2, 0) / self.num_slices
      if self.num_slices > 0
      else 0
    )

  ## memo caches by vertex only - valid because a vertex's result depends solely on
  ## (vertex, quorum_graph, target_set, blocking), never on which path reached it
  ## v-blocking is the same walk with each group's threshold complemented: blocked once more
  ## than len(children)-threshold children are blocked, i.e. effective threshold m-t+1
  def check_threshold(
    self, vertex, quorum_graph, target_set, blocking, memo=None
  ) -> bool:
    if memo is None:
      memo = {}
    if vertex is None:
      return False
    if vertex in memo:
      return memo[vertex]
    if not vertex.startswith("grp:"):
      result = vertex in target_set
    else:
      threshold, children = quorum_graph[vertex]
      count = sum(
        self.check_threshold(c, quorum_graph, target_set, blocking, memo)
        for c in children
      )
      effective_threshold = (
        len(children) - threshold + 1 if blocking else threshold
      )
      result = count >= effective_threshold
    memo[vertex] = result
    return result
