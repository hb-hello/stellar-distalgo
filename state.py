INFINITY = 2 ** 31  ## A large number to represent infinity for ballot counters

class Ballot:
  # A ballot b is a pair of the
  # form b = ⟨n, x⟩, where x != ⊥ is a value and b is a referendum on externalizing x for
  # the slot in question. The value n ≥ 1 is a counter to ensure higher ballot numbers
  # are always available. We use C-like notation b.n and b.x to denote the counter and
  # value fields of ballot b, so that b = ⟨b.n, b.x⟩. Ballots are totally ordered, with b.n
  # more significant than b.x. For convenience, a special invalid null ballot 0 = ⟨0, ⊥⟩
  # is less than all other ballots, and a special counter value infinity is greater than all other
  # counters.
  #? ⊥ ??
  def __init__(self, n=0, x=''):
    self.n = n
    self.x = x

  def __hash__(self):
    return hash((self.n, self.x))

  def __repr__(self):
    return f"Ballot(n={self.n}, x={self.x})"

  ## Adding logic for comparing ballots as Python does not allow object comparisons by default
  def __lt__(self, other):
    if self.n < other.n:
      return True
    elif self.n == other.n:
      return self.x < other.x
    else:
      return False

  def __eq__(self, other):
    return self.n == other.n and self.x == other.x

  def __gt__(self, other):
    return not self == other and not self < other

  # Definition (compatible). Two ballots b1 and b2 are compatible, written b1 ∼ b2, iff
  # b1.x = b2.x and incompatible, written b1 ≁ b2, iff b1.x ≠ b2.x. We also write b1 ≲ b2 or
  # b2 ≳ b1 iff b1 ≤ b2 (or equivalently b2 ≥ b1) and b1 ∼ b2.
  # Similarly, b1 ⋦ b2 or b2 ⋧ b1 means b1 ≤ b2 (or equivalently b2 ≥ b1) and b1 ≁ b2

  def lt_c(self, other):
    return self.n <= other.n and self.x == other.x

  def gt_c(self, other):
    return self.n >= other.n and self.x == other.x

  def lt_nc(self, other):
    return self.n <= other.n and self.x != other.x

  def gt_nc(self, other):
    return self.n >= other.n and self.x != other.x

def extract_fields(msg):
    msg_type = msg[0]

    # Define phi ordering: PREPARE < CONFIRM < EXTERNALIZE
    phi_order = {'PREPARE': 0, 'CONFIRM': 1, 'EXTERNALIZE': 2}

    # Extract fields based on message type (default to 0 if not present)
    if msg_type == 'PREPARE':
      # PREPARE v i b p p2 c.n h.n D
      phi = phi_order['PREPARE']
      b = msg[3] if len(msg) > 3 else Ballot(0, None)
      p = msg[4] if len(msg) > 4 else Ballot(0, None)
      p2 = msg[5] if len(msg) > 5 else Ballot(0, None)
      h_n = msg[7] if len(msg) > 7 else 0
      h = Ballot(h_n, b.x) if h_n != 0 else Ballot(0, None)

    elif msg_type == 'CONFIRM':
      # CONFIRM v i b p.n c.n h.n D
      phi = phi_order['CONFIRM']
      b = msg[3] if len(msg) > 3 else Ballot(INFINITY, None)
      p_n = msg[4] if len(msg) > 4 else 0
      p = Ballot(p_n, b.x) if p_n != 0 else Ballot(0, None)
      p2 = Ballot(0, None)  # p2 = 0 for CONFIRM
      h_n = msg[6] if len(msg) > 6 else 0
      h = Ballot(h_n, b.x) if h_n != 0 else Ballot(0, None)

    elif msg_type == 'EXTERNALIZE':
      # EXTERNALIZE v i x c.n h.n D
      phi = phi_order['EXTERNALIZE']
      x = msg[3] if len(msg) > 3 else None
      b = Ballot(INFINITY, x)
      p = Ballot(INFINITY, x)
      p2 = Ballot(0, None)  # p2 = 0 for EXTERNALIZE
      h_n = msg[5] if len(msg) > 5 else INFINITY
      h = Ballot(h_n, x)
    else:
      ## Unknown message type, return minimum values
      phi = -1
      b = p = p2 = h = Ballot(0, None)

    return (phi, b, p, p2, h)

class State:
  def __init__(self, slot:int, D:tuple):

    self.slot = slot  ## The slot number this state corresponds to
    self.n = 0 ## the nomination round for this slot #? when do we increment this?

    # Fig. 14. Nomination state maintained by node v for each slot
    self.X = set()  # The set of values v has voted to nominate
    self.Y = set()  # The set of values v has accepted as nominated
    self.Z = set()  # The set of values v considers candidate values
    self.N = set()  # The set of the latest nomination message received from each node ## map indexed on node id
    self.v_n = None ## the neighbor with the max priority - recalculated every time nomination round changes
    self.nomination_loop_activated = False  ## flag to indicate whether the nomination loop is active for this slot
    # All four fields are initialized to the empty set.


    # Fig. 16. Ballot state maintained by each node v for each slot
    self.phi = 'PREPARE' # Current phase: one of PREPARE, CONFIRM, or EXTERNALIZE
    self.b = Ballot() # Current ballot that node v is attempting to prepare and commit (b != 0)
    self.p2, self.p = Ballot(), Ballot()  # The twohighest ballots accepted as prepared such that p2 <!~ p,
                            # where p2 = 0 or p = p2 = 0 if there are no such ballots #? what is ~
    self.c, self.h = Ballot(), Ballot()
            # In PREPARE :h is the highest ballot confirmed as prepared, or 0 if none;
            # if c != 0, then c is lowest andh the highest ballot for which
            # vhas voted 'commit' and not accepted 'abort'.
            # In CONFIRM : lowest,highest ballot for which v accepted 'commit'
            # In EXTERNALIZE : lowest, highest ballot for which v confirmed 'commit'
            # Invariant: if c != 0, then c <~h <~ b.
    self.z = None  # Value to use in next ballot. If h = 0, then z is the composite value (see
                # Section 6.1); otherwise, z = h.x. #? init with None
    self.M = set() # Set of the latest ballot message seen from each node - the latest message received from each node #?should be a map indexed on node id
    self.votes = set() ## set of conceptual statements based on messages

    # Each node initializes its slot state by setting phi to PREPARE, b to ⟨0, z⟩,
    # M to empty set, and all other fields (p, p2, c, h) to invalid ballot 0.

  def add_nomination(self, v, X, Y, D):
    # Because X and Y grow monotonically over time, it is possible to determine which of mul-
    # tiple NOMINATE messages from the same node is the latest, independent of network delivery order
    ## return true if the nomination message is new and should be processed, false otherwise
    existing_msg = next((m for m in self.N if m[1] == v), None)
    if existing_msg is None:
      self.N.add((v, frozenset(X), frozenset(Y), D))
      return True
    else:
      if len(existing_msg[1]) < len(X) or len(existing_msg[2]) < len(Y):
        self.N.discard(existing_msg)
        self.N.add((v, frozenset(X), frozenset(Y), D))
        return True
    return False

  def add_message(self, msg):
    # All messages sent by a particular node are totally ordered by ⟨phi, b, p, p2, h⟩, with phi
    # the most significant and h the least significant field. The values of these fields can be
    # determined from messages, as described in Figure 17. All PREPARE messages precede
    # all CONFIRM messages, which in turn precede the single EXTERNALIZE message for a
    # given slot. The ordering makes it possible to ensure M contains only the latest ballot from
    # each node without relying on timing to order the messages, since the network may re-order messages.
    ## return true if the message is new and should be processed, false otherwise
    sender = msg[1]
    phi, b, p, p2, h = extract_fields(msg)
    existing_msg = next((m for m in self.M if m[1] == sender), None)

    if existing_msg is None:
      self.M.add(msg)
      return True
    else:
       if (phi, b, p, p2, h) < extract_fields(existing_msg):
         self.M.discard(existing_msg)
         self.M.add(msg)
         return True
    return False
