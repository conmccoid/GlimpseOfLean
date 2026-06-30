/-
  MonotonicSubsequence.lean
  =========================
  Formalization of the sequence-graph proof that every sequence of 101
  distinct integers contains a monotonic subsequence of length 11.

  PROOF OUTLINE
  -------------------------------------------------
  1.  Define sequence graphs
  2.  Write an algorithm to produce sequence graphs.
    i.  Show the graphs produced by this algorithm relate L-inf distance to MSL.
  3.  Modify this algorithm to prevent overlap in the sequence graphs.
    i.  Show the resulting graphs maintain the L-inf distance connection.
  4.  Show that non-overlapping graphs for sequences of length n² are at least
      n × n, so every root-to-leaf path has L-∞ length ≥ n, giving MSL ≥ n.
  5.  A sequence of length 101 = 10² + 1 therefore has MSL ≥ 11.

  SORRY MAP
  ---------
  Every `sorry` is numbered and has a comment.  They should be discharged in
  order; later sorries depend on earlier ones only through their *statements*.

-/

import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

open List

variable {α : Type*} [LinearOrder α]

/-! ## §1  Sequences and monotonic subsequences -/

section Sequences

/-- A *subsequence* is given by a strictly increasing selection of indices.
list l' is a subsequence of list l iff l' <+ l -/

def StrictlyIncreasing (l : List α) : Prop :=
  l.Pairwise (· < ·)

def StrictlyDecreasing (l : List α) : Prop :=
  l.Pairwise (· > ·)

def IsMonotonic (l : List α) : Prop :=
  StrictlyIncreasing l ∨ StrictlyDecreasing l

end Sequences

/-! ## §2  The 2D rectilinear grid and L-∞ distance -/

section Grid

/-- A node in the rectilinear grid is just a pair of integers. -/
abbrev GridPos := ℤ × ℤ

/-- Two grid positions are *adjacent* (connected by a unit edge) if they
    differ by exactly 1 in each coordinate independently — i.e., they are
    the four diagonal neighbours (NE, NW, SE, SW) in the rectilinear sense. -/
def Adjacent (p q : GridPos) : Prop :=
  (p.1 - q.1).natAbs = 1 ∧ (p.2 - q.2).natAbs = 1

/-- L-∞ distance on the grid. -/
def linfDist (p q : GridPos) : ℕ :=
  max (p.1 - q.1).natAbs (p.2 - q.2).natAbs

lemma adjacent_linf_one {p q : GridPos} (h : Adjacent p q) :
    linfDist p q = 1 := by
  simp [Adjacent, linfDist] at *
  omega

/-- The *direction* of an edge encodes whether the value increases or decreases. -/
inductive Dir | SWNE | NWSE deriving DecidableEq

def dirVec : Dir → ℤ × ℤ
  | Dir.SWNE => ( 1, 1)
  | Dir.NWSE => (-1, 1)

/-- An edge moves northeast or northwest iff the value increases.
    Note that the index always increases, as edges only move left to right. -/
def Dir.valueIncreases : Dir → Prop
  | Dir.SWNE => True
  | Dir.NWSE => False

end Grid

/-! ## §3  Sequence graphs -/

section SequenceGraph

/-!
  A sequence graph is a finite rectilinear graph in which:
    • nodes are labelled by distinct elements of a sequence;
    • an edge from node a to node b goes from SW to NE if value(b) > value(a),
      and NW to SE if value(b) < value(a).

  We represent a sequence graph as a list of nodes (with their grid positions
  and sequence indices) together with an edge relation.
-/

/-- A node carries:
    - `ind`  : which position in the original sequence this node represents;
    - `val`  : the value at that position;
    - `pos`     : where the node sits in the grid. -/
structure SGNode (α : Type*) where
  ind : ℕ
  val : α
  pos : GridPos
  deriving Repr

structure PredicatesSGNode (l : List α) (node : SGNode α): Prop where
  indices : node.ind < l.length
  values  : node.val = l.get ⟨node.ind, indices⟩

/-- An edge in a sequence graph. -/
structure SGEdge (α : Type*) where
  source : SGNode α
  target : SGNode α
  dir : Dir

structure PredicatesSGEdge (edge : SGEdge α): Prop where
  adjacent : Adjacent edge.source.pos edge.target.pos
  dir_val  : edge.dir.valueIncreases ↔ edge.source.val < edge.target.val
  ind_inc  : edge.source.ind < edge.target.ind
  position : edge.target.pos = edge.source.pos + dirVec edge.dir

/-- A *sequence graph* for a list `l` is a collection of nodes and edges
    satisfying the adjacency conditions of Definition 1. -/
structure SequenceGraph (α : Type*) where
  nodes : List (SGNode α)
  edges : List (SGEdge α)

/-- Well-formedness of a sequence graph with respect to a sequence `l`. -/
structure SGWellFormed (l : List α) (G : SequenceGraph α) : Prop where
  graph_nodes : ∀ v ∈ G.nodes, PredicatesSGNode l v
  graph_edges : ∀ e ∈ G.edges, PredicatesSGEdge e
  nodes_nodup : G.nodes.Nodup
  edges_nodup : G.edges.Nodup
  no_duplicate_indices : Function.Injective (fun node : SGNode α => node.ind)

/-- For a well-formed sequence graph, node indices are valid indices into l. -/
lemma SGNode_valid_index {l : List α} {G : SequenceGraph α}
  (wf : SGWellFormed l G) :
  ∀ v ∈ G.nodes, v.ind < l.length := by
    intro v h
    suffices h1 : PredicatesSGNode l v from by
      exact h1.indices
    apply wf.graph_nodes
    exact h

/-- For a well-formed sequence graph, node indices are unique. -/
lemma SGNode_unique_index {l : List α} {G : SequenceGraph α}
  (wf : SGWellFormed l G) :
  ∀ a1 a2 : Fin G.nodes.length, ((G.nodes.get a1).ind = (G.nodes.get a2).ind) → (a1=a2) := by
    intro a1 a2 h
    apply wf.no_duplicate_indices at h
    refine (Nodup.get_inj_iff ?_).mp ?_
    apply wf.nodes_nodup
    exact h

/-- For a well-formed sequence graph, node values equal elements of l. -/
lemma SGNode_seqVal {l : List α} {G : SequenceGraph α}
  (wf : SGWellFormed l G) :
  ∀ v ∈ G.nodes, v.val = l[v.ind]? := by
      intro v h
      suffices h1 : PredicatesSGNode l v from by
        refine List.some_eq_getElem?_iff.mpr ?_
        use SGNode_valid_index wf v h
        simp [h1.values]
      apply wf.graph_nodes
      exact h

end SequenceGraph

/-! ## §4  Branches and paths -/

section Paths

/-- A *path* in a sequence graph is a list of nodes such that each consecutive
    pair is connected by an edge, and the path moves left-to-right
    (every edge goes NE or SE). -/
structure SGPath (G : SequenceGraph α) where
  -- the path is a subgraph
  path : SequenceGraph α
  -- the path is well-formed
  wf {l : List α} : SGWellFormed l path
  lengths : path.edges.length = path.nodes.length - 1
  nodes_subset : ∀ v ∈ path.nodes, v ∈ G.nodes
  edges_subset : ∀ e ∈ path.edges, e ∈ G.edges
  nonempty     : path.nodes ≠ []
  Nodup        : path.nodes.Nodup ∧ path.edges.Nodup
  -- what makes a path? for each node there is one edge that has this node as a source and one that has it as a target
  connected : ∀ i : Fin (path.nodes.length-1),
    (path.edges.get ⟨i,by grind⟩).source=path.nodes.get ⟨i,  by grind⟩ ∧
    (path.edges.get ⟨i,by grind⟩).target=path.nodes.get ⟨i+1,by grind⟩
  unidirectional : ∀ node ∈ path.nodes,
    ((∃ e ∈ path.edges, e.source=node) ↔ (∃! e ∈ path.edges, e.source=node)) ∧
    ((∃ e ∈ path.edges, e.target=node) ↔ (∃! e ∈ path.edges, e.target=node))

/-- For paths in well-formed sequence graphs, node indices are valid indices into l. -/
lemma SGPath_valid_index {l : List α} {G: SequenceGraph α} {p : SGPath G}
  (wf : SGWellFormed l G) :
  ∀ v ∈ p.path.nodes, v.ind < l.length := by
    intro v h
    have hG : v ∈ G.nodes := by
      apply p.nodes_subset
      exact Multiset.mem_coe.mp h
    apply SGNode_valid_index wf
    apply hG

/-- For paths in well-formed sequence graphs, node indices are unique.
    This is a really easy proof, and can probably be done in situ. -/
lemma SGPath_unique_index {l : List α} {G : SequenceGraph α} {p : SGPath G} :
  ∀ a1 a2 : Fin p.path.nodes.length, ((p.path.nodes.get a1).ind = (p.path.nodes.get a2).ind) → (a1=a2) := by
    intro a1 a2 h
    apply SGNode_unique_index p.wf
    exact h
    exact l.append l

/-- For paths in well-formed sequence graphs, node indices are strictly increasing. -/
lemma SGPath_index_increases {l : List α} {G : SequenceGraph α} {p : SGPath G}
  (wf : SGWellFormed l G) :
  StrictlyIncreasing (p.path.nodes.map SGNode.ind) := by
    unfold StrictlyIncreasing
    refine SortedLT.pairwise ?_
    unfold SortedLT
    unfold StrictMono

    have h : ∀ i : Fin (p.path.nodes.length-1),
      (p.path.nodes.get ⟨i,by grind⟩).ind < (p.path.nodes.get ⟨i+1,by grind⟩).ind := by
      intro i
      have hi : i < p.path.edges.length := by
        rw [p.lengths]
        simp_all only [Fin.is_lt]
      let edge := p.path.edges.get ⟨i,by exact hi⟩
      have he : edge.source=(p.path.nodes.get ⟨i,by grind⟩) ∧
        edge.target=(p.path.nodes.get ⟨(i+1),by grind⟩) := by apply p.connected
      -- replace the two nodes with edge.source and edge.target
      rw[←he.1, ←he.2]
      have h_inc : PredicatesSGEdge edge := by
        apply wf.graph_edges
        apply p.edges_subset
        exact get_mem p.path.edges ⟨↑i, hi⟩
      exact h_inc.ind_inc

    intro a b hab
    simp_all
    -- this part provided by Claude; some interesting ideas here
    have key : ∀ n m : ℕ, n < m → ∀ (hn : n < _) (hm : m < _),
      p.path.nodes[n].ind < p.path.nodes[m].ind := by
      intro n m hnm
      induction hnm with
      | refl => exact fun hn hm => h ⟨n, by grind⟩
      | step hnm ih => exact fun hn hm =>
          (ih (by grind) (by grind)).trans (h ⟨_, by grind⟩)
    exact
      Nat.lt_of_succ_le
        (key (↑a) (↑b) hab (length_map SGNode.ind ▸ a.isLt) (length_map SGNode.ind ▸ b.isLt))

/-- Number of SWNE edges in a path (witnesses increasing steps). -/
def SGPath.neCount {G : SequenceGraph α} (p : SGPath G) : ℕ :=
  (p.path.edges.filter (fun e => e.dir == Dir.SWNE)).length

/-- Number of NWSE edges in a path (witnesses decreasing steps). -/
def SGPath.seCount {G : SequenceGraph α} (p : SGPath G) : ℕ :=
  (p.path.edges.filter (fun e => e.dir == Dir.NWSE)).length

/-- A *branch* is a path whose edges are all NE (ascending branch) or all SE
    (descending branch), maximal in the left-to-right direction. -/
def IsBranch {G : SequenceGraph α} (p : SGPath G) : Prop :=
  (∀ e ∈ p.path.edges, e.dir = Dir.SWNE) ∨ (∀ e ∈ p.path.edges, e.dir = Dir.NWSE)

end Paths

/-! ## §5  Paths represent subsequences (Lemma 1) -/

section Lemma1

variable {α : Type*} [LinearOrder α]

/-- **Lemma 1.**  A left-to-right path in a sequence graph represents a
    subsequence of the underlying sequence.

    Proof: left-to-right edges go NE or SE, so consecutive nodes have
    strictly increasing sequence indices, giving a subsequence. -/
lemma path_is_subseq {l : List α} {G : SequenceGraph α}
    (wf : SGWellFormed l G) (p : SGPath G) :
    (p.path.nodes.map SGNode.val) <+ l := by
      rw [List.sublist_iff_exists_fin_orderEmbedding_get_eq]
      have h_length : (map SGNode.val p.path.nodes).length = p.path.nodes.length := by grind
      simp
      let f : Fin p.path.nodes.length ↪o Fin l.length := {
        toFun := fun i : Fin p.path.nodes.length =>
          ⟨(p.path.nodes.get i).ind, by
            apply SGPath_valid_index wf
            exact get_mem p.path.nodes i⟩
        inj' := by
          intro a1 a2 h
          simp_all
          apply SGPath_unique_index
          exact l.append l
          exact h
        map_rel_iff' := by  -- this should be the heart of the proof
          intro a b
          simp
          have hmono : StrictlyIncreasing (p.path.nodes.map SGNode.ind) := SGPath_index_increases wf
          unfold StrictlyIncreasing at hmono
          rw [List.pairwise_iff_get] at hmono
          simp_all
          constructor
          · intro hba
            by_contra hlt
            push_neg at hlt
            have := hmono (Fin.cast (by simp) b) (Fin.cast (by simp) a) (by simpa using hlt)
            simp [Fin.cast] at this
            omega
          · intro hab
            cases Nat.eq_or_lt_of_le hab with
            | inl h => simp [Fin.ext_iff.mpr h]
            | inr h => exact Nat.le_of_lt (hmono (Fin.cast (by simp) a) (Fin.cast (by simp) b) (by simpa using h))
        }
      use (Fin.castOrderIso (by simp)).toOrderEmbedding.trans f
      intro ix
      have hix : ix < p.path.nodes.length := by grind
      have hl : p.path.nodes[↑ix].ind < l.length := by
        apply SGPath_valid_index wf
        exact mem_of_getElem rfl
      simp_all
      show p.path.nodes[↑ix].val = l[p.path.nodes[↑ix].ind]
      have hexact := SGNode_seqVal (l:=l) p.wf p.path.nodes[ix] (mem_of_getElem rfl)
      grind only [= Fin.getElem_fin, = getElem?_pos]
  -- sorry [3]: Construct the index list from p.nodes.map SGNode.seqIdx,
  -- show it is strictly increasing using leftToRight + edge_dir_idx,
  -- and that the values match using node_vals.

end Lemma1

/-! ## §6  Paths witness monotonic subsequences (Lemmas 3 & 4) -/

section Lemma4

variable {α : Type*} [LinearOrder α]

/-!
  The key lemma.  For the *overlapping* construction (Lemma 3 in the paper)
  the argument is direct.  Lemma 4 handles the *non-overlapping* corrected
  construction; the extra work is the recursive branch-splicing argument.

  We state a single lemma covering both cases.
-/

/-- **Lemma 4.**  For any left-to-right path `p` in a (possibly overlap-
    corrected) constructed sequence graph, there exists:
    - a strictly increasing subsequence of `l` of length ≥ `p.neCount`, and
    - a strictly decreasing subsequence of `l` of length ≥ `p.seCount`.  -/
lemma path_witnesses_monotone {l : List α} {G : SequenceGraph α}
    (wf : SGWellFormed l G) (p : SGPath G) :
    (∃ sub : List α, p.neCount ≤ sub.length ∧
      StrictlyIncreasing sub ∧ IsSubseq l sub) ∧
    (∃ sub : List α, p.seCount ≤ sub.length ∧
      StrictlyDecreasing sub ∧ IsSubseq l sub) := by
  /-
    sorry [4]: This is the main combinatorial content.
    Structure of the proof:
    (a) If the path has no overlap-placed nodes, proceed by induction on path
        length: each NE edge extends the increasing subsequence, each SE edge
        extends the decreasing one (using edge_dir_val from wf).
    (b) If there is at least one overlap-placed node, locate the first such
        point (the "root of the subgraph" in the paper's language).
        Split the path into a prefix (up to the overlap point) and a suffix
        (the subgraph rooted there).
        Apply case (a) recursively to the prefix along each of the two
        competing branches (first branch: descending; second branch: ascending).
        Apply this lemma recursively to the suffix.
        Splice the monotone subsequences:
          - increasing: second-branch witness ++ subgraph increasing witness
            (valid because all overlap-placed nodes are larger than the last
            node of the second branch);
          - decreasing: first-branch witness ++ subgraph decreasing witness
            (valid because overlap-placed nodes are smaller than the subgraph
            root).
  -/
  sorry

end Lemma4

/-! ## §7  The construction algorithm -/

section Construction

variable {α : Type*} [LinearOrder α]

/-!
  The paper gives two versions of the construction algorithm:
    (A) the simple version, which may produce overlapping nodes;
    (B) the corrected version, which avoids overlaps by treating a would-be
        overlapping node as if it belonged to the existing branch at that
        position (without adding an edge).

  We formalize version (B) directly, since it is the one used in the proof.
  The algorithm builds a tree rooted at the first element; subsequent elements
  are inserted by walking the tree from the root.
-/

/-- The state of the construction: the graph built so far, plus the current
    root position (always the westernmost node). -/
structure ConstructState (α : Type*) [LinearOrder α] where
  graph   : SequenceGraph α
  rootPos : GridPos

/-- Insert one element into the construction state.
    `insertIdx` and `insertVal` are the sequence index and value of the new
    element.  The function walks from the root, choosing NE/SE at each step,
    until it finds an empty grid position (no existing node there), then places
    a new node.  If the target position is already occupied, it continues from
    that node without adding an edge (the overlap-correction step). -/
noncomputable def insertElement (s : ConstructState α)
    (insertIdx : ℕ) (insertVal : α) : ConstructState α := by
  -- sorry [5]: Implement the walk-and-insert algorithm.
  -- The termination argument is that the walk strictly increases the
  -- x-coordinate at each step, and x is bounded by the number of nodes
  -- already placed.
  exact s  -- placeholder

/-- Build the full construction graph for a list. -/
noncomputable def buildGraph (l : List α) : SequenceGraph α :=
  match l with
  | []     => { nodes := [], edges := [] }
  | x :: xs =>
    let init : ConstructState α :=
      { graph   := { nodes := [⟨0, x, (0, 0)⟩], edges := [] }
        rootPos := (0, 0) }
    let final := xs.enum.foldl
      (fun s ⟨i, v⟩ => insertElement s (i + 1) v) init
    final.graph

/-- The graph produced by the construction is well-formed. -/
lemma buildGraph_wellFormed (l : List α) (hd : l.Nodup) :
    SGWellFormed l (buildGraph l) := by
  -- sorry [6]: by induction on l, using the invariants of insertElement.
  sorry

/-- The construction graph is non-overlapping: no two nodes share a position. -/
lemma buildGraph_noOverlap (l : List α) (hd : l.Nodup) :
    ((buildGraph l).nodes.map SGNode.pos).Nodup := by
  -- sorry [7]: by induction, the overlap-correction step ensures this.
  sorry

end Construction

/-! ## §8  Shape of the construction graph (Theorem 2) -/

section Shape

variable {α : Type*} [LinearOrder α]

/-!
  The paper argues that a non-overlapping constructed graph for a sequence of
  length n² forms at least an n × n rectilinear grid.  We encode this by
  showing that the graph contains a path from the root of L-∞ length ≥ n,
  which by Lemma 4 gives a monotonic subsequence of length ≥ n.

  More precisely: the root-to-leaf paths of the construction tree cover a
  rectilinear region.  If the total node count is > (n-1)², then the region
  cannot fit in an (n-1) × (n-1) square, so some path has L-∞ length ≥ n.
-/

/-- The L-∞ length of a path equals its number of edges (since every edge
    has L-∞ length 1). -/
lemma path_linf_length {G : SequenceGraph α} (p : SGPath G) :
    linfDist p.nodes.head! (p.nodes.getLast!) = p.edges.length := by
  -- sorry [8]: by induction on p.edges, using adjacent_linf_one.
  sorry

/-- The number of nodes in an n × n rectilinear grid is n². -/
lemma grid_node_count (n : ℕ) : (Finset.Icc (0 : ℤ) n ×ˢ Finset.Icc 0 n).card = (n + 1) ^ 2 := by
  simp [Finset.card_product]

/-- If the construction graph has more than n² nodes, some root-to-leaf path
    has more than n edges.

    Proof: the nodes of a non-overlapping construction graph all lie in the
    rectilinear cone reachable from the root; the maximum number of nodes in
    an n-deep tree of this shape is n².  More nodes forces deeper paths. -/
lemma deep_path_of_many_nodes {l : List α} (hd : l.Nodup) (n : ℕ)
    (hlen : n ^ 2 < l.length) :
    ∃ p : SGPath (buildGraph l), n < p.edges.length := by
  -- sorry [9]: The key geometric argument.
  -- The construction tree has at most (depth)² nodes at each level.
  -- With > n² nodes and non-overlapping placement, the tree must reach
  -- depth > n.  Formalize by tracking the bounding box of placed nodes
  -- and arguing by contradiction.
  sorry

/-- A deep path gives a long monotonic subsequence. -/
lemma long_monotone_of_deep_path {l : List α} (hd : l.Nodup)
    (p : SGPath (buildGraph l)) (hdeep : n < p.edges.length) :
    (∃ sub : List α, n + 1 ≤ sub.length ∧ StrictlyIncreasing sub ∧ IsSubseq l sub) ∨
    (∃ sub : List α, n + 1 ≤ sub.length ∧ StrictlyDecreasing sub ∧ IsSubseq l sub) := by
  -- A path of length > n has either > n NE edges or > n SE edges.
  have hne_or_se : n < p.neCount ∨ n < p.seCount := by
    -- sorry [10]: p.neCount + p.seCount = p.edges.length, so one exceeds n/2;
    -- more precisely since neCount + seCount = edges.length > n, one of them
    -- exceeds n/2, but we need one to exceed n.  Actually we need the stronger
    -- claim from the paper: the path goes entirely NE or entirely SE
    -- (it is a branch), giving neCount = length or seCount = length.
    -- For a general path we instead appeal to the paper's argument that the
    -- maximum of neCount and seCount is at least ceil(length / 2), but the
    -- paper actually uses branches, where one of them equals length.
    -- Use the branch decomposition: every root-to-leaf path in the
    -- construction tree IS a branch (all-NE or all-SE), so one of neCount,
    -- seCount equals p.edges.length > n.
    sorry
  obtain (hne | hse) := hne_or_se
  · left
    obtain ⟨sub, hlen, hinc, hsubseq⟩ :=
      (path_witnesses_monotone (buildGraph_wellFormed l hd) p).1
    exact ⟨sub, by omega, hinc, hsubseq⟩
  · right
    obtain ⟨sub, hlen, hdec, hsubseq⟩ :=
      (path_witnesses_monotone (buildGraph_wellFormed l hd) p).2
    exact ⟨sub, by omega, hdec, hsubseq⟩

end Shape

/-! ## §9  Main theorems -/

section MainTheorems

variable {α : Type*} [LinearOrder α]

/-- **Theorem 2.**  A sequence of length > n² with distinct elements has a
    monotonic subsequence of length ≥ n + 1. -/
theorem monotone_subseq_of_length_sq
    {l : List α} (hd : l.Nodup) (n : ℕ) (hlen : n ^ 2 < l.length) :
    ∃ sub : List α,
      n + 1 ≤ sub.length ∧ IsMonotonic sub ∧ IsSubseq l sub := by
  obtain ⟨p, hdeep⟩ := deep_path_of_many_nodes hd n hlen
  obtain (⟨sub, hsublen, hinc, hsubseq⟩ | ⟨sub, hsublen, hdec, hsubseq⟩) :=
    long_monotone_of_deep_path hd p hdeep
  · exact ⟨sub, hsublen, Or.inl hinc, hsubseq⟩
  · exact ⟨sub, hsublen, Or.inr hdec, hsubseq⟩

/-- **Theorem 1.**  Every sequence of 101 distinct elements contains a
    monotonic subsequence of length at least 11. -/
theorem monotone_subseq_length_11
    (l : List α) (hd : l.Nodup) (hlen : l.length = 101) :
    ∃ sub : List α,
      11 ≤ sub.length ∧ IsMonotonic sub ∧ IsSubseq l sub := by
  apply monotone_subseq_of_length_sq hd 10
  simp [hlen]

end MainTheorems
