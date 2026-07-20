/-
  MonotonicSubsequence.lean
  =========================
  Formalization of the sequence-graph proof that every sequence of 101
  distinct integers contains a monotonic subsequence of length 11.

  PROOF OUTLINE (following the paper `101.pdf`)
  ---------------------------------------------
  1.  Define sequence graphs (Definition 1) and left-to-right paths.
  2.  Lemma 1: paths represent subsequences.                          [PROVED]
  3.  Interface `ConstructedGraph`: the properties the non-overlapping
      construction of §2.1 guarantees, including the conclusion of
      Lemmas 3 & 4 (the `monotone` field).
  4.  Position arithmetic: along a path the grid offset of the last node
      is `(#NE + #SE, #NE - #SE)`, so distinct positions ⇔ distinct
      (#NE, #SE) counts for root paths.                               [PROVED]
  5.  Pigeonhole: more than n² nodes at distinct positions force a root
      path with ≥ n NE edges or ≥ n SE edges.                         [PROVED]
  6.  Theorems 2 and 1.                                           [PROVED]
  7.  The walk-and-insert construction algorithm (§2.1 of the paper) is
      implemented, and its correctness is proved:
      * buildGraph_wellFormed : Lemma 2                            [PROVED]
      * buildGraph_complete   : one node per sequence element      [PROVED]
      * buildGraph_noOverlap  : the §2.1 correction works          [PROVED]
      * buildGraph_rootpath   : the construction is a tree         [PROVED]
      * buildGraph_monotone   : Lemmas 3 & 4                       [PROVED]

  The file is sorry-free.  The paper's branch-splicing proof of Lemma 4 is
  replaced by the monotone-witness invariant `MonoInv` — every node at
  grid position (x, y) carries an increasing witness of length at least
  (x+y)/2 + 1 and a decreasing one of length at least (x−y)/2 + 1 — which
  is maintained along the insertion walk by two accumulator lists; see the
  blueprint comment before `MonoInv` in §9.

  NOTES ON CHANGES TO EARLIER STATEMENTS
  --------------------------------------
  * `SGWellFormed.no_duplicate_indices` demanded injectivity of `SGNode.ind`
    on the whole type `SGNode α`, which is unsatisfiable; it is now
    `indices_nodup : (G.nodes.map SGNode.ind).Nodup`.
  * `SGPath.wf` quantified over every list `l`, which made `SGPath`
    uninhabited (any nonempty path would need `v.ind < List.length []`).
    Well-formedness of a path is now *derived* from well-formedness of the
    ambient graph (`SGPath.wellFormed`).  The `unidirectional` field was
    dropped: it follows from `connected` + `Nodup`.
  * `dirVec Dir.NWSE` was `(-1, 1)`; a southeast step in a left-to-right
    graph is `(1, -1)` (x = index direction always increases).
  * `ConstructedGraph.ordering` ("first edge NWSE ⇒ last value < first
    value") is FALSE for the real non-overlapping construction: for
    4761235 (Figure 3b) the path 4→7→6→2 starts with a NE edge yet ends
    below its first value, because 2 was placed due to overlap.  This is
    precisely why the paper needs the splicing argument of Lemma 4.  The
    interface now carries the *conclusion* of Lemmas 3 & 4 (`monotone`),
    to be discharged by the construction correctness proof.
  * `path_witnesses_monotone` (old Lemma 4) was stated for arbitrary
    well-formed graphs, where it is false (e.g. the single path with
    values 1,5,0,4,-1,3 has 3 NE edges but no increasing subsequence of
    length 3).  It only holds for constructed graphs.
  * The monotone-subsequence bounds are strengthened from `neCount` to
    `neCount + 1` (a path with n NE edges visits n+1 increasing values);
    Theorem 2 needs this to get MSL n+1 from n² + 1 elements.
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

/-- The grid step of an edge: first coordinate is the index direction (always
    increases going left to right), second is the value direction. -/
def dirVec : Dir → ℤ × ℤ
  | Dir.SWNE => (1, 1)
  | Dir.NWSE => (1, -1)

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
    - `pos`  : where the node sits in the grid. -/
structure SGNode (α : Type*) where
  ind : ℕ
  val : α
  pos : GridPos
  deriving Repr

structure PredicatesSGNode (l : List α) (node : SGNode α) : Prop where
  indices : node.ind < l.length
  values  : node.val = l.get ⟨node.ind, indices⟩

/-- An edge in a sequence graph. -/
structure SGEdge (α : Type*) where
  source : SGNode α
  target : SGNode α
  dir : Dir

structure PredicatesSGEdge (edge : SGEdge α) : Prop where
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
  edges_nodup : G.edges.Nodup
  /-- No two nodes represent the same sequence index (this also implies
      `G.nodes.Nodup`, see `SGWellFormed.nodes_nodup`). -/
  indices_nodup : (G.nodes.map SGNode.ind).Nodup
  nonempty : G.nodes ≠ []

/-- In a well-formed graph, distinct nodes carry distinct indices. -/
lemma SGWellFormed.ind_injOn {l : List α} {G : SequenceGraph α}
    (wf : SGWellFormed l G) :
    ∀ v ∈ G.nodes, ∀ w ∈ G.nodes, v.ind = w.ind → v = w :=
  List.inj_on_of_nodup_map wf.indices_nodup

/-- For a well-formed sequence graph, the node list has no duplicates. -/
lemma SGWellFormed.nodes_nodup {l : List α} {G : SequenceGraph α}
    (wf : SGWellFormed l G) : G.nodes.Nodup :=
  List.Nodup.of_map _ wf.indices_nodup

/-- For a well-formed sequence graph, node indices are valid indices into l. -/
lemma SGNode_valid_index {l : List α} {G : SequenceGraph α}
    (wf : SGWellFormed l G) :
    ∀ v ∈ G.nodes, v.ind < l.length := by
  intro v h
  exact (wf.graph_nodes v h).indices

/-- For a well-formed sequence graph, node indices are unique. -/
lemma SGNode_unique_index {l : List α} {G : SequenceGraph α}
    (wf : SGWellFormed l G) :
    ∀ a1 a2 : Fin G.nodes.length,
      ((G.nodes.get a1).ind = (G.nodes.get a2).ind) → (a1 = a2) := by
  intro a1 a2 h
  refine (Nodup.get_inj_iff wf.nodes_nodup).mp ?_
  exact wf.ind_injOn _ (get_mem _ _) _ (get_mem _ _) h

/-- For a well-formed sequence graph, node values equal elements of l. -/
lemma SGNode_seqVal {l : List α} {G : SequenceGraph α}
    (wf : SGWellFormed l G) :
    ∀ v ∈ G.nodes, v.val = l[v.ind]? := by
  intro v h
  have h1 : PredicatesSGNode l v := wf.graph_nodes v h
  refine List.some_eq_getElem?_iff.mpr ?_
  exact ⟨h1.indices, by simp [h1.values]⟩

end SequenceGraph

/-! ## §4  Branches and paths -/

section Paths

/-- A *path* in a sequence graph is a list of nodes such that each consecutive
    pair is connected by an edge, and the path moves left-to-right
    (every edge goes NE or SE). -/
structure SGPath (G : SequenceGraph α) where
  -- the path is a subgraph
  path : SequenceGraph α
  lengths : path.edges.length = path.nodes.length - 1
  nodes_subset : ∀ v ∈ path.nodes, v ∈ G.nodes
  edges_subset : ∀ e ∈ path.edges, e ∈ G.edges
  nonempty     : path.nodes ≠ []
  Nodup        : path.nodes.Nodup ∧ path.edges.Nodup
  -- what makes a path? edge i connects node i to node i+1
  connected : ∀ i : Fin (path.nodes.length - 1),
    (path.edges.get ⟨i, by grind⟩).source = path.nodes.get ⟨i, by grind⟩ ∧
    (path.edges.get ⟨i, by grind⟩).target = path.nodes.get ⟨i + 1, by grind⟩

/-- A path in a well-formed graph is itself a well-formed graph. -/
lemma SGPath.wellFormed {l : List α} {G : SequenceGraph α}
    (p : SGPath G) (wf : SGWellFormed l G) : SGWellFormed l p.path where
  graph_nodes v hv := wf.graph_nodes v (p.nodes_subset v hv)
  graph_edges e he := wf.graph_edges e (p.edges_subset e he)
  edges_nodup := p.Nodup.2
  indices_nodup := by
    refine List.Nodup.map_on ?_ p.Nodup.1
    intro x hx y hy hxy
    exact wf.ind_injOn x (p.nodes_subset x hx) y (p.nodes_subset y hy) hxy
  nonempty := p.nonempty

/-- The one-node path at a node of the graph. -/
def SGPath.single {G : SequenceGraph α} (v : SGNode α) (hv : v ∈ G.nodes) :
    SGPath G where
  path := ⟨[v], []⟩
  lengths := rfl
  nodes_subset := by simpa using hv
  edges_subset := by simp
  nonempty := by simp
  Nodup := ⟨List.nodup_singleton _, List.nodup_nil⟩
  connected := fun i => i.elim0

/-- A path lifts along an inclusion of graphs. -/
def SGPath.lift {G G' : SequenceGraph α} (p : SGPath G)
    (hn : ∀ v ∈ G.nodes, v ∈ G'.nodes) (he : ∀ e ∈ G.edges, e ∈ G'.edges) :
    SGPath G' where
  path := p.path
  lengths := p.lengths
  nodes_subset := fun v hv => hn v (p.nodes_subset v hv)
  edges_subset := fun e h => he e (p.edges_subset e h)
  nonempty := p.nonempty
  Nodup := p.Nodup
  connected := p.connected

omit [LinearOrder α] in
@[simp] lemma SGPath.lift_path {G G' : SequenceGraph α} (p : SGPath G)
    (hn : ∀ v ∈ G.nodes, v ∈ G'.nodes) (he : ∀ e ∈ G.edges, e ∈ G'.edges) :
    (p.lift hn he).path = p.path := rfl

/-- Extend a path by one edge at its right end. -/
def SGPath.snoc {G : SequenceGraph α} (p : SGPath G) (e : SGEdge α)
    (heG : e ∈ G.edges) (htG : e.target ∈ G.nodes)
    (hsrc : e.source = p.path.nodes.getLast p.nonempty)
    (hnew : e.target ∉ p.path.nodes) (henew : e ∉ p.path.edges) :
    SGPath G where
  path := ⟨p.path.nodes ++ [e.target], p.path.edges ++ [e]⟩
  lengths := by
    have := List.length_pos_of_ne_nil p.nonempty
    have := p.lengths
    simp
    omega
  nodes_subset := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact p.nodes_subset v hv
    · rw [List.mem_singleton] at hv
      subst hv
      exact htG
  edges_subset := by
    intro e' he'
    rcases List.mem_append.mp he' with he' | he'
    · exact p.edges_subset e' he'
    · rw [List.mem_singleton] at he'
      subst he'
      exact heG
  nonempty := by simp
  Nodup := by
    constructor
    · rw [List.nodup_append]
      refine ⟨p.Nodup.1, List.nodup_singleton _, ?_⟩
      intro a ha b hb hab
      rw [List.mem_singleton] at hb
      subst hb
      subst hab
      exact hnew ha
    · rw [List.nodup_append]
      refine ⟨p.Nodup.2, List.nodup_singleton _, ?_⟩
      intro a ha b hb hab
      rw [List.mem_singleton] at hb
      subst hb
      subst hab
      exact henew ha
  connected := by
    intro i
    have hn0 := List.length_pos_of_ne_nil p.nonempty
    have hm := p.lengths
    have hilt := i.isLt
    simp only [List.length_append, List.length_cons, List.length_nil] at hilt
    have hi : (i : ℕ) < p.path.nodes.length := by omega
    simp only [List.get_eq_getElem]
    by_cases hcase : (i : ℕ) < p.path.edges.length
    · have he1 : (p.path.edges ++ [e])[(i : ℕ)]'(by simp; omega) =
          p.path.edges[(i : ℕ)]'hcase := List.getElem_append_left hcase
      have hn1 : (p.path.nodes ++ [e.target])[(i : ℕ)]'(by simp; omega) =
          p.path.nodes[(i : ℕ)]'hi := List.getElem_append_left hi
      have hn2 : (p.path.nodes ++ [e.target])[(i : ℕ) + 1]'(by simp; omega) =
          p.path.nodes[(i : ℕ) + 1]'(by omega) := List.getElem_append_left (by omega)
      have hc := p.connected ⟨i, by omega⟩
      simp only [List.get_eq_getElem] at hc
      rw [he1, hn1, hn2]
      exact hc
    · have hieq : (i : ℕ) = p.path.edges.length := by omega
      have he1 : (p.path.edges ++ [e])[(i : ℕ)]'(by simp; omega) = e := by
        rw [List.getElem_append_right (by omega)]
        exact List.getElem_singleton _
      have hn1 : (p.path.nodes ++ [e.target])[(i : ℕ)]'(by simp; omega) =
          p.path.nodes[(i : ℕ)]'hi := List.getElem_append_left hi
      have hn2 : (p.path.nodes ++ [e.target])[(i : ℕ) + 1]'(by simp; omega) = e.target := by
        rw [List.getElem_append_right (by omega)]
        exact List.getElem_singleton _
      rw [he1, hn1, hn2]
      refine ⟨?_, rfl⟩
      rw [hsrc, List.getLast_eq_getElem]
      congr 1
      omega

omit [LinearOrder α] in
@[simp] lemma SGPath.snoc_head {G : SequenceGraph α} (p : SGPath G) (e : SGEdge α)
    (heG : e ∈ G.edges) (htG : e.target ∈ G.nodes)
    (hsrc : e.source = p.path.nodes.getLast p.nonempty)
    (hnew : e.target ∉ p.path.nodes) (henew : e ∉ p.path.edges) :
    (p.snoc e heG htG hsrc hnew henew).path.nodes.head
        (p.snoc e heG htG hsrc hnew henew).nonempty =
      p.path.nodes.head p.nonempty :=
  List.head_append_of_ne_nil p.nonempty

omit [LinearOrder α] in
@[simp] lemma SGPath.snoc_getLast {G : SequenceGraph α} (p : SGPath G) (e : SGEdge α)
    (heG : e ∈ G.edges) (htG : e.target ∈ G.nodes)
    (hsrc : e.source = p.path.nodes.getLast p.nonempty)
    (hnew : e.target ∉ p.path.nodes) (henew : e ∉ p.path.edges) :
    (p.snoc e heG htG hsrc hnew henew).path.nodes.getLast
        (p.snoc e heG htG hsrc hnew henew).nonempty = e.target :=
  List.getLast_concat

/-- For paths in well-formed sequence graphs, node indices are valid indices into l. -/
lemma SGPath_valid_index {l : List α} {G : SequenceGraph α} {p : SGPath G}
    (wf : SGWellFormed l G) :
    ∀ v ∈ p.path.nodes, v.ind < l.length := by
  intro v h
  exact SGNode_valid_index wf v (p.nodes_subset v h)

/-- For paths in well-formed sequence graphs, node indices are unique. -/
lemma SGPath_unique_index {l : List α} {G : SequenceGraph α} {p : SGPath G}
    (wf : SGWellFormed l G) :
    ∀ a1 a2 : Fin p.path.nodes.length,
      ((p.path.nodes.get a1).ind = (p.path.nodes.get a2).ind) → (a1 = a2) :=
  SGNode_unique_index (p.wellFormed wf)

/-- For paths in well-formed sequence graphs, node indices are strictly increasing. -/
lemma SGPath_index_increases {l : List α} {G : SequenceGraph α} {p : SGPath G}
    (wf : SGWellFormed l G) :
    StrictlyIncreasing (p.path.nodes.map SGNode.ind) := by
  unfold StrictlyIncreasing
  refine SortedLT.pairwise ?_
  unfold SortedLT
  unfold StrictMono
  have h : ∀ i : Fin (p.path.nodes.length - 1),
      (p.path.nodes.get ⟨i, by grind⟩).ind < (p.path.nodes.get ⟨i + 1, by grind⟩).ind := by
    intro i
    have hi : i < p.path.edges.length := by
      rw [p.lengths]
      simp_all only [Fin.is_lt]
    let edge := p.path.edges.get ⟨i, by exact hi⟩
    have he : edge.source = (p.path.nodes.get ⟨i, by grind⟩) ∧
        edge.target = (p.path.nodes.get ⟨(i + 1), by grind⟩) := by apply p.connected
    rw [← he.1, ← he.2]
    have h_inc : PredicatesSGEdge edge := by
      apply wf.graph_edges
      apply p.edges_subset
      exact get_mem p.path.edges ⟨↑i, hi⟩
    exact h_inc.ind_inc
  intro a b hab
  simp_all
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

omit [LinearOrder α] in
/-- Every edge is NE or SE, so the two counts partition the edges. -/
lemma SGPath.neCount_add_seCount {G : SequenceGraph α} (p : SGPath G) :
    p.neCount + p.seCount = p.path.edges.length := by
  unfold SGPath.neCount SGPath.seCount
  induction p.path.edges with
  | nil => simp
  | cons e t ih =>
    cases h : e.dir <;> simp [h] <;> omega

/-- A *branch* is a path whose edges are all NE (ascending branch) or all SE
    (descending branch), maximal in the left-to-right direction. -/
def IsBranch {G : SequenceGraph α} (p : SGPath G) : Prop :=
  (∀ e ∈ p.path.edges, e.dir = Dir.SWNE) ∨ (∀ e ∈ p.path.edges, e.dir = Dir.NWSE)

end Paths

/-! ## §5  Paths represent subsequences (Lemma 1) -/

section Lemma1

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
      exact SGPath_unique_index wf a1 a2 h
    map_rel_iff' := by
      intro a b
      simp
      have hmono : StrictlyIncreasing (p.path.nodes.map SGNode.ind) := SGPath_index_increases wf
      unfold StrictlyIncreasing at hmono
      rw [List.pairwise_iff_get] at hmono
      simp_all
      constructor
      · intro hba
        by_contra hlt
        push Not at hlt
        have := hmono (Fin.cast (by simp) b) (Fin.cast (by simp) a) (by simpa using hlt)
        simp [Fin.cast] at this
        linarith
      · intro hab
        cases Nat.eq_or_lt_of_le hab with
        | inl h => simp [Fin.ext_iff.mpr h]
        | inr h =>
          exact Nat.le_of_lt (hmono (Fin.cast (by simp) a) (Fin.cast (by simp) b)
            (by simpa using h))
    }
  use (Fin.castOrderIso (by simp)).toOrderEmbedding.trans f
  intro ix
  have hix : ix < p.path.nodes.length := by grind only
  have hl : p.path.nodes[↑ix].ind < l.length := by
    apply SGPath_valid_index wf
    exact mem_of_getElem rfl
  simp_all
  change p.path.nodes[↑ix].val = l[p.path.nodes[↑ix].ind]
  have hexact := SGNode_seqVal (p.wellFormed wf) p.path.nodes[ix] (mem_of_getElem rfl)
  grind only [= Fin.getElem_fin, = getElem?_pos]

end Lemma1

/-! ## §6  Constructed graphs: the interface (Lemmas 2, 3 & 4) -/

section ConstructedGraph

/-!
  `ConstructedGraph l` packages the properties that the non-overlapping
  construction of §2.1 of the paper guarantees:

  * it is a sequence graph for `l` (Lemma 2: `wf`);
  * it has one node per element of `l` (`complete`);
  * no two nodes share a grid position (`no_overlap`, the point of §2.1);
  * every node is reachable from the root by a left-to-right path
    (`rootpath` — the constructed graphs are trees);
  * the conclusion of Lemmas 3 & 4: every left-to-right path witnesses a
    monotonically increasing subsequence longer than its NE edge count and
    a monotonically decreasing subsequence longer than its SE edge count
    (`monotone`).

  The `monotone` field cannot be replaced by a path-local ordering
  invariant: nodes placed due to overlap break every such invariant (see
  the note at the top of the file), and the paper's Lemma 4 repairs this
  with a global recursive splicing argument.  That argument belongs to the
  construction correctness proof (`buildGraph_monotone` below).
-/

structure ConstructedGraph (l : List α) where
  G : SequenceGraph α
  wf : SGWellFormed l G
  /-- The westernmost node, representing the first element of the sequence. -/
  root : SGNode α
  /-- The constructed graph is a tree: every node is reached from the root
      by a left-to-right path. -/
  rootpath : ∀ v ∈ G.nodes, ∃ p : SGPath G,
    p.path.nodes.head p.nonempty = root ∧ p.path.nodes.getLast p.nonempty = v
  /-- The §2.1 overlap correction: no two nodes share a grid position. -/
  no_overlap : (G.nodes.map SGNode.pos).Nodup
  /-- Every element of the sequence is represented by a node. -/
  complete : G.nodes.length = l.length
  /-- **Lemmas 3 & 4 of the paper.**  A path with k NE (resp. SE) edges
      witnesses an increasing (decreasing) subsequence of length k + 1. -/
  monotone : ∀ p : SGPath G,
    (∃ sub : List α, p.neCount + 1 ≤ sub.length ∧ StrictlyIncreasing sub ∧ sub <+ l) ∧
    (∃ sub : List α, p.seCount + 1 ≤ sub.length ∧ StrictlyDecreasing sub ∧ sub <+ l)

/-- **Lemmas 3 & 4.** For any path `p` in a constructed sequence graph, there is
    - a strictly increasing subsequence of `l` of length > `p.neCount`, and
    - a strictly decreasing subsequence of `l` of length > `p.seCount`. -/
lemma constructed_path_monotone {l : List α} (CG : ConstructedGraph l)
    (p : SGPath CG.G) :
    (∃ sub : List α, p.neCount + 1 ≤ sub.length ∧ StrictlyIncreasing sub ∧ sub <+ l) ∧
    (∃ sub : List α, p.seCount + 1 ≤ sub.length ∧ StrictlyDecreasing sub ∧ sub <+ l) :=
  CG.monotone p

end ConstructedGraph

/-! ## §7  Position arithmetic along paths -/

section PositionArithmetic

/-!
  Every edge moves one unit east; a NE edge moves one unit north and a SE
  edge one unit south.  Hence the offset of the `j`-th node of a path from
  the head node is `(#NE + #SE, #NE - #SE)` over the first `j` edges.
  This is the formal content of the paper's identification of MSL with
  L-∞ distance, and it drives the pigeonhole argument of §8.
-/

/-- The position of the `j`-th node of a path, in terms of the edge-direction
    counts of the first `j` edges. -/
lemma SGPath.pos_formula {l : List α} {G : SequenceGraph α} (p : SGPath G)
    (wf : SGWellFormed l G) :
    ∀ j (hj : j < p.path.nodes.length),
      (p.path.nodes[j]'hj).pos =
        (p.path.nodes[0]'(Nat.pos_of_ne_zero (by simp [p.nonempty]))).pos +
          ((((p.path.edges.take j).filter (fun e => e.dir == Dir.SWNE)).length +
            ((p.path.edges.take j).filter (fun e => e.dir == Dir.NWSE)).length,
           (((p.path.edges.take j).filter (fun e => e.dir == Dir.SWNE)).length : ℤ) -
            ((p.path.edges.take j).filter (fun e => e.dir == Dir.NWSE)).length) : ℤ × ℤ) := by
  intro j
  induction j with
  | zero =>
    intro hj
    simp
  | succ j ih =>
    intro hj
    have hj0 : j < p.path.nodes.length := by omega
    have hje : j < p.path.edges.length := by
      have := p.lengths
      omega
    have hconn := p.connected ⟨j, by omega⟩
    have hedge : PredicatesSGEdge (p.path.edges[j]'hje) :=
      wf.graph_edges _ (p.edges_subset _ (List.getElem_mem hje))
    have hpos : (p.path.nodes[j + 1]'hj).pos =
        (p.path.nodes[j]'hj0).pos + dirVec ((p.path.edges[j]'hje).dir) := by
      have h1 := hconn.1
      have h2 := hconn.2
      simp only [List.get_eq_getElem] at h1 h2
      rw [← h2, ← h1]
      exact hedge.position
    have htake : p.path.edges.take (j + 1) =
        p.path.edges.take j ++ [p.path.edges[j]'hje] := by
      rw [List.take_add_one]
      simp [List.getElem?_eq_getElem hje]
    have hNE1 : ((p.path.edges.take (j + 1)).filter (fun e => e.dir == Dir.SWNE)).length =
        ((p.path.edges.take j).filter (fun e => e.dir == Dir.SWNE)).length +
          (if (p.path.edges[j]'hje).dir = Dir.SWNE then 1 else 0) := by
      rw [htake, List.filter_append, List.length_append]
      rcases hd : (p.path.edges[j]'hje).dir <;> simp [hd, beq_iff_eq]
    have hSE1 : ((p.path.edges.take (j + 1)).filter (fun e => e.dir == Dir.NWSE)).length =
        ((p.path.edges.take j).filter (fun e => e.dir == Dir.NWSE)).length +
          (if (p.path.edges[j]'hje).dir = Dir.NWSE then 1 else 0) := by
      rw [htake, List.filter_append, List.length_append]
      rcases hd : (p.path.edges[j]'hje).dir <;> simp [hd, beq_iff_eq]
    rw [hpos, ih hj0, hNE1, hSE1]
    rcases hdir : (p.path.edges[j]'hje).dir <;>
      simp [dirVec, Prod.ext_iff] <;>
      omega

/-- The grid offset between the endpoints of a path is
    `(#NE + #SE, #NE - #SE)`. -/
lemma SGPath.getLast_pos {l : List α} {G : SequenceGraph α} (p : SGPath G)
    (wf : SGWellFormed l G) :
    (p.path.nodes.getLast p.nonempty).pos =
      (p.path.nodes.head p.nonempty).pos +
        (((p.neCount + p.seCount : ℕ) : ℤ), ((p.neCount : ℤ) - p.seCount)) := by
  have hlen : 0 < p.path.nodes.length := List.length_pos_of_ne_nil p.nonempty
  have hlast : p.path.nodes.length - 1 < p.path.nodes.length := by omega
  have := p.pos_formula wf (p.path.nodes.length - 1) hlast
  have htake : p.path.edges.take (p.path.nodes.length - 1) = p.path.edges := by
    rw [← p.lengths]
    exact List.take_length
  rw [List.getLast_eq_getElem, List.head_eq_getElem]
  simp only [htake] at this
  rw [this]
  simp [SGPath.neCount, SGPath.seCount]

/-- The L-∞ length of a path equals its number of edges (since every edge
    has L-∞ length 1).  This identifies path length with L-∞ distance. -/
lemma path_linf_length {l : List α} {G : SequenceGraph α}
    (wf : SGWellFormed l G) (p : SGPath G) :
    linfDist (p.path.nodes.head p.nonempty).pos (p.path.nodes.getLast p.nonempty).pos =
      p.path.edges.length := by
  have h := p.getLast_pos wf
  have hcount := p.neCount_add_seCount
  rw [linfDist, h]
  obtain ⟨x, y⟩ := (p.path.nodes.head p.nonempty).pos
  simp
  omega

end PositionArithmetic

/-! ## §8  The pigeonhole argument (Theorem 2, geometric part) -/

section Pigeonhole

/-!
  The paper argues that a non-overlapping constructed graph for a sequence
  of length > n² cannot fit in an n × n grid.  Formally: map each node `v`
  to the pair `(#NE, #SE)` of some root path ending at `v`.  By
  `SGPath.getLast_pos`, this pair determines the position of `v`, and by
  `no_overlap` positions determine nodes — so the map is injective.  If
  every root path had fewer than n NE edges and fewer than n SE edges, the
  map would inject > n² nodes into the n × n grid `range n ×ˢ range n`.
-/

/-- If a non-overlapping constructed graph has more than n² nodes, some
    root path has at least n NE edges or at least n SE edges. -/
lemma wide_path_of_many_nodes {l : List α} (CG : ConstructedGraph l) (n : ℕ)
    (hcount : n ^ 2 < CG.G.nodes.length) :
    ∃ p : SGPath CG.G, n ≤ p.neCount ∨ n ≤ p.seCount := by
  by_contra hcon
  simp only [not_exists, not_or, not_le] at hcon
  classical
  have hnodup : CG.G.nodes.Nodup := CG.wf.nodes_nodup
  have hcardS : CG.G.nodes.toFinset.card = CG.G.nodes.length :=
    List.toFinset_card_of_nodup hnodup
  choose pathOf hhead hlast using CG.rootpath
  let f : SGNode α → ℕ × ℕ := fun v =>
    if h : v ∈ CG.G.nodes then ((pathOf v h).neCount, (pathOf v h).seCount)
    else (0, 0)
  have hmaps : ∀ v ∈ CG.G.nodes.toFinset,
      f v ∈ Finset.range n ×ˢ Finset.range n := by
    intro v hv
    rw [List.mem_toFinset] at hv
    have h1 := hcon (pathOf v hv)
    simp only [f, dif_pos hv, Finset.mem_product, Finset.mem_range]
    exact ⟨h1.1, h1.2⟩
  have hlt : (Finset.range n ×ˢ Finset.range n).card < CG.G.nodes.toFinset.card := by
    rw [Finset.card_product, Finset.card_range, hcardS, ← pow_two]
    exact hcount
  obtain ⟨v, hv, w, hw, hvw, hf⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  rw [List.mem_toFinset] at hv hw
  -- the (#NE, #SE) pair determines the position
  have hposv : v.pos = CG.root.pos +
      ((((pathOf v hv).neCount + (pathOf v hv).seCount : ℕ) : ℤ),
        (((pathOf v hv).neCount : ℤ) - (pathOf v hv).seCount)) := by
    have h := (pathOf v hv).getLast_pos CG.wf
    rw [hlast v hv, hhead v hv] at h
    exact h
  have hposw : w.pos = CG.root.pos +
      ((((pathOf w hw).neCount + (pathOf w hw).seCount : ℕ) : ℤ),
        (((pathOf w hw).neCount : ℤ) - (pathOf w hw).seCount)) := by
    have h := (pathOf w hw).getLast_pos CG.wf
    rw [hlast w hw, hhead w hw] at h
    exact h
  have hcounts : (pathOf v hv).neCount = (pathOf w hw).neCount ∧
      (pathOf v hv).seCount = (pathOf w hw).seCount := by
    have : f v = f w := hf
    simpa [f, dif_pos hv, dif_pos hw, Prod.ext_iff] using this
  have hpos : v.pos = w.pos := by
    rw [hposv, hposw, hcounts.1, hcounts.2]
  exact hvw (List.inj_on_of_nodup_map CG.no_overlap hv hw hpos)

end Pigeonhole

/-! ## §9  The construction algorithm (§2.1 of the paper) -/

section Construction

/-!
  The paper gives two versions of the construction algorithm:
    (A) the simple version, which may produce overlapping nodes;
    (B) the corrected version (§2.1), which avoids overlaps by treating a
        node already occupying the target position as if it belonged to the
        current branch (without adding an edge).

  We implement version (B) directly, since it is the one used in the proof.
  Each new element walks east from the root: at each node it compares
  values (up if larger, down if smaller) and moves to the target position;
  if that position is occupied it continues the walk from the occupying
  node, otherwise it places a new node there, adjacent to the node the walk
  came from.  The walk always moves east, so `G.nodes.length` steps of fuel
  suffice to reach an empty position.
-/

/-- The grid position one step from `cur` in the direction determined by
    comparing values: up (NE) if `v` is larger, down (SE) otherwise. -/
def stepDir (cur : SGNode α) (v : α) : Dir :=
  if cur.val < v then Dir.SWNE else Dir.NWSE

/-- The node of `G` at position `pos`, if any. -/
def findNode? (G : SequenceGraph α) (pos : GridPos) : Option (SGNode α) :=
  G.nodes.find? (fun n => decide (n.pos = pos))

/-- One walk of the corrected algorithm: walk east from `cur`, moving up or
    down according to value comparisons, continuing through occupied
    positions (the §2.1 correction), until an empty position is found;
    place the node for `(idx, v)` there, adjacent to the last node visited. -/
def walkInsert (idx : ℕ) (v : α) : ℕ → SequenceGraph α → SGNode α → SequenceGraph α
  | 0, G, _ => G  -- fuel exhausted; never reached from a valid state
  | fuel + 1, G, cur =>
    let dir := stepDir cur v
    let tpos := cur.pos + dirVec dir
    match findNode? G tpos with
    | some next => walkInsert idx v fuel G next
    | none =>
      let node : SGNode α := ⟨idx, v, tpos⟩
      { nodes := G.nodes ++ [node]
        edges := G.edges ++ [⟨cur, node, dir⟩] }

/-- Insert one element into the graph by walking from the root. -/
def insertElement (root : SGNode α) (G : SequenceGraph α)
    (idx : ℕ) (v : α) : SequenceGraph α :=
  walkInsert idx v (G.nodes.length + 1) G root

/-- Build the full construction graph for a list. -/
def buildGraph : List α → SequenceGraph α
  | [] => { nodes := [], edges := [] }
  | x :: xs =>
    let root : SGNode α := ⟨0, x, (0, 0)⟩
    (xs.zipIdx 1).foldl
      (fun G vi => insertElement root G vi.2 vi.1)
      { nodes := [root], edges := [] }

/-!
  Correctness of the construction.  Together these lemmas discharge
  Lemmas 2, 3 and 4 of the paper.  Each is proved by induction on the
  construction, maintaining invariants of the intermediate states: every
  walk starts at the root, visits nodes of strictly increasing
  x-coordinate (the termination measure), and places each new node at a
  previously empty position adjacent to its parent.
-/

/-- Each step of the walk stays adjacent to the previous position. -/
lemma adjacent_step (p : GridPos) (d : Dir) : Adjacent p (p + dirVec d) := by
  cases d <;> simp [Adjacent, dirVec]

/-- `walkInsert` only ever appends nodes. -/
lemma walkInsert_nodes_mono (idx : ℕ) (v : α) :
    ∀ (fuel : ℕ) (G : SequenceGraph α) (cur : SGNode α),
      ∃ t, (walkInsert idx v fuel G cur).nodes = G.nodes ++ t := by
  intro fuel
  induction fuel with
  | zero => exact fun G cur => ⟨[], by simp [walkInsert]⟩
  | succ fuel ih =>
    intro G cur
    simp only [walkInsert]
    rcases hfind : findNode? G (cur.pos + dirVec (stepDir cur v)) with _ | next
    · exact ⟨_, rfl⟩
    · exact ih G next

/-- The invariant maintained while building the graph: everything inserted so
    far satisfies the sequence-graph predicates, edge targets are nodes, and
    all sequence indices used so far are below `bound`. -/
structure BuildInv (l : List α) (bound : ℕ) (G : SequenceGraph α) : Prop where
  nodes_pred : ∀ v ∈ G.nodes, PredicatesSGNode l v
  edges_pred : ∀ e ∈ G.edges, PredicatesSGEdge e
  tgt_mem : ∀ e ∈ G.edges, e.target ∈ G.nodes
  edges_nodup : G.edges.Nodup
  indices_nodup : (G.nodes.map SGNode.ind).Nodup
  nonempty : G.nodes ≠ []
  ind_lt : ∀ v ∈ G.nodes, v.ind < bound

lemma BuildInv.mono {l : List α} {b b' : ℕ} {G : SequenceGraph α}
    (h : BuildInv l b G) (hb : b ≤ b') : BuildInv l b' G :=
  { h with ind_lt := fun v hv => lt_of_lt_of_le (h.ind_lt v hv) hb }

lemma BuildInv.wellFormed {l : List α} {G : SequenceGraph α}
    (h : BuildInv l l.length G) : SGWellFormed l G where
  graph_nodes := h.nodes_pred
  graph_edges := h.edges_pred
  edges_nodup := h.edges_nodup
  indices_nodup := h.indices_nodup
  nonempty := h.nonempty

/-- The walk preserves the build invariant, raising the bound to `idx + 1`. -/
lemma walkInsert_inv {l : List α} {idx : ℕ} (hidx : idx < l.length) {v : α}
    (hv : v = l.get ⟨idx, hidx⟩) :
    ∀ (fuel : ℕ) (G : SequenceGraph α) (cur : SGNode α),
      BuildInv l idx G → cur ∈ G.nodes →
      BuildInv l (idx + 1) (walkInsert idx v fuel G cur) := by
  intro fuel
  induction fuel with
  | zero => exact fun G cur h _ => h.mono (Nat.le_succ idx)
  | succ fuel ih =>
    intro G cur h hcur
    simp only [walkInsert]
    rcases hfind : findNode? G (cur.pos + dirVec (stepDir cur v)) with _ | next
    · refine ⟨?_, ?_, ?_, ?_, ?_, by simp, ?_⟩
      · intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · exact h.nodes_pred w hw
        · rw [List.mem_singleton] at hw
          subst hw
          exact ⟨hidx, hv⟩
      · intro e he
        rcases List.mem_append.mp he with he | he
        · exact h.edges_pred e he
        · rw [List.mem_singleton] at he
          subst he
          refine ⟨adjacent_step _ _, ?_, h.ind_lt cur hcur, rfl⟩
          by_cases hlt : cur.val < v
          · simp [stepDir, hlt, Dir.valueIncreases]
          · simp [stepDir, hlt, Dir.valueIncreases]
      · intro e he
        rcases List.mem_append.mp he with he | he
        · exact List.mem_append_left _ (h.tgt_mem e he)
        · rw [List.mem_singleton] at he
          subst he
          simp
      · rw [List.nodup_append]
        refine ⟨h.edges_nodup, List.nodup_singleton _, ?_⟩
        intro e he e' he' heq
        rw [List.mem_singleton] at he'
        subst he'
        subst heq
        have := h.ind_lt _ (h.tgt_mem _ he)
        simp at this
      · simp only [List.map_append, List.map_cons, List.map_nil]
        rw [List.nodup_append]
        refine ⟨h.indices_nodup, List.nodup_singleton _, ?_⟩
        intro q hq b hb heq
        rw [List.mem_singleton] at hb
        subst hb
        subst heq
        obtain ⟨w, hw, hwq⟩ := List.mem_map.mp hq
        have := h.ind_lt w hw
        omega
      · intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · exact lt_of_lt_of_le (h.ind_lt w hw) (Nat.le_succ idx)
        · rw [List.mem_singleton] at hw
          subst hw
          exact Nat.lt_succ_self idx
    · have hfind' : G.nodes.find?
          (fun n => decide (n.pos = cur.pos + dirVec (stepDir cur v))) = some next := hfind
      exact ih G next h (List.mem_of_find?_eq_some hfind')

/-- The fold over the remaining elements preserves the invariant. -/
lemma build_loop_inv (l : List α) (root : SGNode α) :
    ∀ (k b : ℕ) (G : SequenceGraph α), l.length - b ≤ k → b ≤ l.length →
      BuildInv l b G → root ∈ G.nodes →
      BuildInv l l.length
        (((l.drop b).zipIdx b).foldl
          (fun G vi => insertElement root G vi.2 vi.1) G) := by
  intro k
  induction k with
  | zero =>
    intro b G hk hble h _
    have hdrop : l.drop b = [] := List.drop_eq_nil_of_le (by omega)
    rw [hdrop]
    exact h.mono (by omega)
  | succ k ih =>
    intro b G hk hble h hroot
    by_cases hb : b < l.length
    · rw [List.drop_eq_getElem_cons hb, List.zipIdx_cons, List.foldl_cons]
      refine ih (b + 1) _ (by omega) (by omega) ?_ ?_
      · exact walkInsert_inv hb (by simp) _ G root h hroot
      · obtain ⟨t, ht⟩ := walkInsert_nodes_mono b l[b] (G.nodes.length + 1) G root
        change root ∈ (walkInsert b l[b] (G.nodes.length + 1) G root).nodes
        rw [ht]
        exact List.mem_append_left _ hroot
    · have hdrop : l.drop b = [] := List.drop_eq_nil_of_le (by omega)
      rw [hdrop]
      exact h.mono (by omega)

/-- The invariant holds for the initial one-node graph. -/
lemma buildInv_init (x : α) (xs : List α) :
    BuildInv (x :: xs) 1 ⟨[⟨0, x, (0, 0)⟩], []⟩ := by
  refine ⟨?_, by simp, by simp, List.nodup_nil, by simp, by simp, ?_⟩
  · intro w hw
    rw [List.mem_singleton] at hw
    subst hw
    exact ⟨by simp, rfl⟩
  · intro w hw
    rw [List.mem_singleton] at hw
    subst hw
    exact Nat.lt_succ_self 0

/-- **Lemma 2.** The construction produces a sequence graph. -/
lemma buildGraph_wellFormed (l : List α) (hne : l ≠ []) :
    SGWellFormed l (buildGraph l) := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hloop := build_loop_inv (x :: xs) ⟨0, x, (0, 0)⟩ (x :: xs).length 1
    ⟨[⟨0, x, (0, 0)⟩], []⟩ (by omega) (by simp) (buildInv_init x xs) (by simp)
  exact hloop.wellFormed

/-- Counting with a stricter predicate that some member fails strictly
    lowers the count.  (Used for the termination measure of the walk.) -/
lemma countP_lt_countP {β : Type*} {l : List β} {p q : β → Bool}
    (himp : ∀ b ∈ l, p b = true → q b = true) {a : β} (ha : a ∈ l)
    (hpa : p a = false) (hqa : q a = true) :
    l.countP p < l.countP q := by
  induction l with
  | nil => simp at ha
  | cons b t ih =>
    have hle : t.countP p ≤ t.countP q :=
      List.countP_mono_left (fun x hx h => himp x (List.mem_cons_of_mem _ hx) h)
    rcases List.mem_cons.mp ha with rfl | hat
    · simp [hpa, hqa]
      omega
    · have hlt := ih (fun x hx h => himp x (List.mem_cons_of_mem _ hx) h) hat
      have hb : (if p b then 1 else 0) ≤ (if q b then 1 else 0) := by
        by_cases hpb : p b = true
        · simp [hpb, himp b List.mem_cons_self hpb]
        · simp [Bool.eq_false_iff.mpr hpb]
      simp only [List.countP_cons]
      omega

/-- With enough fuel (more than the number of nodes strictly east of the
    starting node) the walk terminates by placing exactly one new node.
    This is the termination argument: every step moves one unit east, to a
    node of the graph, so at most `G.nodes.length` steps can find a node. -/
lemma walkInsert_length (idx : ℕ) (v : α) :
    ∀ (fuel : ℕ) (G : SequenceGraph α) (cur : SGNode α),
      G.nodes.countP (fun n => cur.pos.1 < n.pos.1) < fuel →
      (walkInsert idx v fuel G cur).nodes.length = G.nodes.length + 1 := by
  intro fuel
  induction fuel with
  | zero => omega
  | succ fuel ih =>
    intro G cur hfuel
    simp only [walkInsert]
    rcases hfind : findNode? G (cur.pos + dirVec (stepDir cur v)) with _ | next
    · simp
    · apply ih
      have hfind' : G.nodes.find?
          (fun n => decide (n.pos = cur.pos + dirVec (stepDir cur v))) = some next := hfind
      have hmem : next ∈ G.nodes := List.mem_of_find?_eq_some hfind'
      have hpos : next.pos = cur.pos + dirVec (stepDir cur v) := by
        have := List.find?_some hfind'
        simpa using this
      have hdv : (dirVec (stepDir cur v)).1 = 1 := by
        cases stepDir cur v <;> rfl
      have hx : next.pos.1 = cur.pos.1 + 1 := by
        rw [hpos, Prod.fst_add, hdv]
      have hlt : G.nodes.countP (fun n => next.pos.1 < n.pos.1) <
          G.nodes.countP (fun n => cur.pos.1 < n.pos.1) := by
        refine countP_lt_countP (fun b _ hb => ?_) hmem ?_ ?_
        · simp only [decide_eq_true_eq] at *
          omega
        · simp
        · simp [hx]
      omega

/-- Inserting an element adds exactly one node. -/
lemma insertElement_length (root : SGNode α) (G : SequenceGraph α)
    (idx : ℕ) (v : α) :
    (insertElement root G idx v).nodes.length = G.nodes.length + 1 := by
  apply walkInsert_length
  have := List.countP_le_length (l := G.nodes) (p := fun n => decide (root.pos.1 < n.pos.1))
  omega

/-- Every element of the sequence gets exactly one node. -/
lemma buildGraph_complete (l : List α) :
    (buildGraph l).nodes.length = l.length := by
  cases l with
  | nil => simp [buildGraph]
  | cons x xs =>
    simp only [buildGraph]
    suffices h : ∀ (ys : List (α × ℕ)) (G : SequenceGraph α),
        ((ys.foldl (fun G vi => insertElement ⟨0, x, (0, 0)⟩ G vi.2 vi.1) G).nodes.length)
          = G.nodes.length + ys.length by
      rw [h]
      simp
      omega
    intro ys
    induction ys with
    | nil => simp
    | cons y t ih =>
      intro G
      simp only [List.foldl_cons]
      rw [ih, insertElement_length]
      simp only [List.length_cons]
      omega

/-- The walk places new nodes only at previously empty positions, so
    position-distinctness is preserved. -/
lemma walkInsert_noOverlap (idx : ℕ) (v : α) :
    ∀ (fuel : ℕ) (G : SequenceGraph α) (cur : SGNode α),
      (G.nodes.map SGNode.pos).Nodup →
      ((walkInsert idx v fuel G cur).nodes.map SGNode.pos).Nodup := by
  intro fuel
  induction fuel with
  | zero => exact fun G cur h => h
  | succ fuel ih =>
    intro G cur h
    simp only [walkInsert]
    rcases hfind : findNode? G (cur.pos + dirVec (stepDir cur v)) with _ | next
    · have hfind' : G.nodes.find?
          (fun n => decide (n.pos = cur.pos + dirVec (stepDir cur v))) = none := hfind
      have hempty : ∀ n ∈ G.nodes, n.pos ≠ cur.pos + dirVec (stepDir cur v) := by
        intro n hn hEq
        exact (List.find?_eq_none.mp hfind' n hn) (by simp [hEq])
      simp only [List.map_append, List.map_cons, List.map_nil]
      rw [List.nodup_append]
      refine ⟨h, List.nodup_singleton _, ?_⟩
      intro q hq b hb hqb
      obtain ⟨n, hn, hnpos⟩ := List.mem_map.mp hq
      rw [List.mem_singleton] at hb
      exact hempty n hn (by rw [hnpos, hqb, hb])
    · exact ih G next h

/-- **§2.1.** The corrected construction is non-overlapping. -/
lemma buildGraph_noOverlap (l : List α) :
    ((buildGraph l).nodes.map SGNode.pos).Nodup := by
  cases l with
  | nil => simp [buildGraph]
  | cons x xs =>
    simp only [buildGraph]
    suffices h : ∀ (ys : List (α × ℕ)) (G : SequenceGraph α),
        (G.nodes.map SGNode.pos).Nodup →
        (((ys.foldl (fun G vi => insertElement ⟨0, x, (0, 0)⟩ G vi.2 vi.1) G).nodes.map
          SGNode.pos).Nodup) by
      exact h _ _ (by simp)
    intro ys
    induction ys with
    | nil => exact fun G h => h
    | cons y t ih =>
      intro G h
      simp only [List.foldl_cons]
      exact ih _ (walkInsert_noOverlap _ _ _ _ _ h)

/-- Reachability from the root by a left-to-right path. -/
def RootReach (root : SGNode α) (G : SequenceGraph α) : Prop :=
  ∀ v ∈ G.nodes, ∃ p : SGPath G,
    p.path.nodes.head p.nonempty = root ∧ p.path.nodes.getLast p.nonempty = v

/-- The walk preserves root-reachability: old paths lift to the extended
    graph, and the newly placed node is reached by extending the path to its
    parent with the new edge. -/
lemma walkInsert_rootReach {l : List α} {idx : ℕ} {v : α} {root : SGNode α} :
    ∀ (fuel : ℕ) (G : SequenceGraph α) (cur : SGNode α),
      BuildInv l idx G → cur ∈ G.nodes → RootReach root G →
      RootReach root (walkInsert idx v fuel G cur) := by
  intro fuel
  induction fuel with
  | zero => exact fun G cur _ _ hr => hr
  | succ fuel ih =>
    intro G cur h hcur hr
    simp only [walkInsert]
    rcases hfind : findNode? G (cur.pos + dirVec (stepDir cur v)) with _ | next
    · intro w hw
      have hn : ∀ u ∈ G.nodes,
          u ∈ G.nodes ++ [(⟨idx, v, cur.pos + dirVec (stepDir cur v)⟩ : SGNode α)] :=
        fun u hu => List.mem_append_left _ hu
      have he : ∀ e ∈ G.edges, e ∈ G.edges ++
          [(⟨cur, ⟨idx, v, cur.pos + dirVec (stepDir cur v)⟩, stepDir cur v⟩ : SGEdge α)] :=
        fun e heq => List.mem_append_left _ heq
      rcases List.mem_append.mp hw with hw | hw
      · obtain ⟨p, hph, hpl⟩ := hr w hw
        exact ⟨p.lift hn he, hph, hpl⟩
      · rw [List.mem_singleton] at hw
        subst hw
        obtain ⟨p, hph, hpl⟩ := hr cur hcur
        refine ⟨(p.lift hn he).snoc
          ⟨cur, ⟨idx, v, cur.pos + dirVec (stepDir cur v)⟩, stepDir cur v⟩
          (List.mem_append_right _ (by simp)) (List.mem_append_right _ (by simp))
          hpl.symm ?_ ?_, ?_, ?_⟩
        · intro hmem
          exact absurd (h.ind_lt _ (p.nodes_subset _ hmem)) (lt_irrefl idx)
        · intro hmem
          exact absurd (h.ind_lt _ (h.tgt_mem _ (p.edges_subset _ hmem))) (lt_irrefl idx)
        · rw [SGPath.snoc_head]
          exact hph
        · rw [SGPath.snoc_getLast]
    · have hfind' : G.nodes.find?
          (fun n => decide (n.pos = cur.pos + dirVec (stepDir cur v))) = some next := hfind
      exact ih G next h (List.mem_of_find?_eq_some hfind') hr

/-- The fold over the remaining elements preserves root-reachability. -/
lemma build_loop_root (l : List α) (root : SGNode α) :
    ∀ (k b : ℕ) (G : SequenceGraph α), l.length - b ≤ k → b ≤ l.length →
      BuildInv l b G → root ∈ G.nodes → RootReach root G →
      RootReach root
        (((l.drop b).zipIdx b).foldl
          (fun G vi => insertElement root G vi.2 vi.1) G) := by
  intro k
  induction k with
  | zero =>
    intro b G hk hble h hroot hr
    have hdrop : l.drop b = [] := List.drop_eq_nil_of_le (by omega)
    rw [hdrop]
    exact hr
  | succ k ih =>
    intro b G hk hble h hroot hr
    by_cases hb : b < l.length
    · rw [List.drop_eq_getElem_cons hb, List.zipIdx_cons, List.foldl_cons]
      obtain ⟨t, ht⟩ := walkInsert_nodes_mono b l[b] (G.nodes.length + 1) G root
      refine ih (b + 1) _ (by omega) (by omega) ?_ ?_ ?_
      · exact walkInsert_inv hb (by simp) _ G root h hroot
      · change root ∈ (walkInsert b l[b] (G.nodes.length + 1) G root).nodes
        rw [ht]
        exact List.mem_append_left _ hroot
      · exact walkInsert_rootReach _ G root h hroot hr
    · have hdrop : l.drop b = [] := List.drop_eq_nil_of_le (by omega)
      rw [hdrop]
      exact hr

/-- The construction is a tree rooted at the node of the first element. -/
lemma buildGraph_rootpath (l : List α) (hne : l ≠ []) :
    ∀ v ∈ (buildGraph l).nodes, ∃ p : SGPath (buildGraph l),
      p.path.nodes.head p.nonempty = ⟨0, l.head hne, (0, 0)⟩ ∧
      p.path.nodes.getLast p.nonempty = v := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hr0 : RootReach ⟨0, x, (0, 0)⟩ ⟨[⟨0, x, (0, 0)⟩], []⟩ := by
    intro w hw
    rw [List.mem_singleton] at hw
    subst hw
    exact ⟨SGPath.single _ (by simp), rfl, rfl⟩
  have hloop := build_loop_root (x :: xs) ⟨0, x, (0, 0)⟩ (x :: xs).length 1
    ⟨[⟨0, x, (0, 0)⟩], []⟩ (by omega) (by simp) (buildInv_init x xs) (by simp) hr0
  exact hloop

/-!
  ### Lemmas 3 & 4: the monotone-witness invariant

  Blueprint (working out the roadmap in the file header).  Write
  `u(P) = P.1 + P.2` and `w(P) = P.1 - P.2` for a grid position `P` — twice
  the "northeast" and "southeast" coordinates; the root sits at `(0, 0)`.

  * Node invariant `MonoInv`: every node `n` of the graph carries
    - a strictly increasing sublist of `l.take (n.ind + 1)` ending in
      `n.val` of length at least `u(n.pos)/2 + 1` (`HasIncEnding`), and
    - a strictly decreasing one of length at least `w(n.pos)/2 + 1`
      (`HasDecEnding`), and
    - `0 ≤ u(n.pos)` and `0 ≤ w(n.pos)`.
  * Walk invariant (`walkInsert_monoInv`): while inserting the value `v`
    with index `idx`, the walk carries two accumulator lists:
    - `inc`, strictly increasing, inside `l.take idx`, all elements `< v`,
      with `u(current position) ≤ 2·|inc|`;
    - `dec`, strictly decreasing, all elements `> v`, with
      `w(current position) ≤ 2·|dec|`.
    Stepping up through a node `c` (that is, `c.val < v`) moves to a
    position with `u` larger by 2 and `w` unchanged, so `inc` is replaced
    by `c`'s own increasing witness — its elements are `≤ c.val < v` and
    its length bound is exactly what is needed — while `dec` is kept.
    Stepping down mirrors this; there `v < c.val` needs `l.Nodup`.
    Nodes reached through the §2.1 overlap correction need no special
    treatment: the invariant only mentions the walk's grid position, and
    this is what replaces the paper's branch-splicing argument.
  * Placement: the new node's witnesses are `_ ++ [v]`, one side extending
    the parent's witness, the other extending the accumulator; the length
    bounds match the new position exactly.
  * `buildGraph_monotone`: for a path from `a` to `b` with `k` northeast
    edges, `SGPath.getLast_pos` gives `u(b.pos) = u(a.pos) + 2k ≥ 2k`, so
    `b`'s increasing witness has length `≥ k + 1`; it is a sublist of
    `l.take (b.ind + 1) <+ l`.  Southeast edges mirror this via `w`.
-/

omit [LinearOrder α] in
/-- Appending an element that is `R`-above a pairwise list. -/
lemma pairwise_append_singleton {R : α → α → Prop} {t : List α} {v : α}
    (h : t.Pairwise R) (hall : ∀ a ∈ t, R a v) : (t ++ [v]).Pairwise R := by
  rw [List.pairwise_append]
  refine ⟨h, List.pairwise_singleton _ _, ?_⟩
  intro a ha b hb
  rw [List.mem_singleton] at hb
  subst hb
  exact hall a ha

omit [LinearOrder α] in
/-- In a pairwise-related list, every element is the last or related to it. -/
lemma pairwise_getLast {R : α → α → Prop} :
    ∀ {t : List α}, t.Pairwise R → ∀ {c : α}, t.getLast? = some c →
      ∀ a ∈ t, a = c ∨ R a c := by
  intro t
  induction t with
  | nil =>
    intro _ c hc
    simp at hc
  | cons b t ih =>
    intro h c hc a ha
    cases t with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hc
      rw [List.mem_singleton] at ha
      subst hc
      subst ha
      exact Or.inl rfl
    | cons b' t' =>
      rw [List.getLast?_cons_cons] at hc
      rcases List.mem_cons.mp ha with rfl | ha
      · exact Or.inr ((List.pairwise_cons.mp h).1 c (List.mem_of_getLast? hc))
      · exact ih (List.pairwise_cons.mp h).2 hc a ha

omit [LinearOrder α] in
/-- Shorter prefixes are sublists of longer ones. -/
lemma take_sublist_take {l : List α} {j k : ℕ} (h : j ≤ k) :
    l.take j <+ l.take k := by
  calc l.take j = (l.take k).take j := by rw [List.take_take, Nat.min_eq_left h]
  _ <+ l.take k := List.take_sublist _ _

omit [LinearOrder α] in
/-- Splitting one element off a prefix. -/
lemma take_succ_eq_take_append {l : List α} {idx : ℕ} (h : idx < l.length) :
    l.take (idx + 1) = l.take idx ++ [l[idx]] := by
  rw [List.take_add_one]
  simp [List.getElem?_eq_getElem h]

/-- Node `n` carries a strictly increasing subsequence of `l` ending at its
    own entry, of length at least `(n.pos.1 + n.pos.2)/2 + 1`. -/
def HasIncEnding (l : List α) (n : SGNode α) : Prop :=
  ∃ inc : List α, StrictlyIncreasing inc ∧ inc <+ l.take (n.ind + 1) ∧
    inc.getLast? = some n.val ∧ n.pos.1 + n.pos.2 + 2 ≤ 2 * (inc.length : ℤ)

/-- Node `n` carries a strictly decreasing subsequence of `l` ending at its
    own entry, of length at least `(n.pos.1 - n.pos.2)/2 + 1`. -/
def HasDecEnding (l : List α) (n : SGNode α) : Prop :=
  ∃ dec : List α, StrictlyDecreasing dec ∧ dec <+ l.take (n.ind + 1) ∧
    dec.getLast? = some n.val ∧ n.pos.1 - n.pos.2 + 2 ≤ 2 * (dec.length : ℤ)

/-- The monotone-witness invariant of the construction (see the blueprint
    above): every node carries both witnesses and sits in the nonnegative
    cone spanned by the two diagonal directions. -/
def MonoInv (l : List α) (G : SequenceGraph α) : Prop :=
  ∀ n ∈ G.nodes, HasIncEnding l n ∧ HasDecEnding l n ∧
    0 ≤ n.pos.1 + n.pos.2 ∧ 0 ≤ n.pos.1 - n.pos.2

/-- The walk preserves the monotone-witness invariant.  The two accumulator
    lists witness the two coordinates of the walk's current position; see
    the blueprint above for the bookkeeping in each case. -/
lemma walkInsert_monoInv {l : List α} (hd : l.Nodup) {idx : ℕ}
    (hidx : idx < l.length) {v : α} (hv : v = l.get ⟨idx, hidx⟩) :
    ∀ (fuel : ℕ) (G : SequenceGraph α) (cur : SGNode α) (inc dec : List α),
      BuildInv l idx G → cur ∈ G.nodes → MonoInv l G →
      StrictlyIncreasing inc → inc <+ l.take idx → (∀ a ∈ inc, a < v) →
      cur.pos.1 + cur.pos.2 ≤ 2 * (inc.length : ℤ) →
      StrictlyDecreasing dec → dec <+ l.take idx → (∀ a ∈ dec, v < a) →
      cur.pos.1 - cur.pos.2 ≤ 2 * (dec.length : ℤ) →
      MonoInv l (walkInsert idx v fuel G cur) := by
  intro fuel
  induction fuel with
  | zero =>
    intro G cur inc dec _ _ hm _ _ _ _ _ _ _ _
    exact hm
  | succ fuel ih =>
    intro G cur inc dec hB hcur hm hi1 hi2 hi3 hi4 hde1 hde2 hde3 hde4
    have hcuridx : cur.ind < idx := hB.ind_lt cur hcur
    obtain ⟨⟨incc, hc1, hc2, hc3, hc4⟩, ⟨decc, hg1, hg2, hg3, hg4⟩, hcu, hcv⟩ :=
      hm cur hcur
    have hccle : ∀ a ∈ incc, a ≤ cur.val := fun a ha =>
      (pairwise_getLast hc1 hc3 a ha).elim le_of_eq le_of_lt
    have hgcge : ∀ a ∈ decc, cur.val ≤ a := fun a ha =>
      (pairwise_getLast hg1 hg3 a ha).elim (fun h => h.symm.le) (fun h => h.le)
    have hc2' : incc <+ l.take idx := hc2.trans (take_sublist_take (by omega))
    have hg2' : decc <+ l.take idx := hg2.trans (take_sublist_take (by omega))
    have hvne : ¬cur.val < v → v < cur.val := by
      intro hnlt
      have hcval : cur.val = l.get ⟨cur.ind, by omega⟩ :=
        (hB.nodes_pred cur hcur).values
      refine lt_of_le_of_ne (not_lt.mp hnlt) ?_
      intro heq
      rw [hv, hcval] at heq
      have := (List.Nodup.get_inj_iff hd).mp heq
      simp [Fin.ext_iff] at this
      omega
    have hvl : v = l[idx] := by rw [hv]; simp
    have htakev : l.take (idx + 1) = l.take idx ++ [v] := by
      rw [take_succ_eq_take_append hidx, ← hvl]
    simp only [walkInsert]
    rcases hfind : findNode? G (cur.pos + dirVec (stepDir cur v)) with _ | next
    · -- placement of the new node
      intro n hn
      rcases List.mem_append.mp hn with hn | hn
      · exact hm n hn
      · rw [List.mem_singleton] at hn
        subst hn
        by_cases hlt : cur.val < v
        · -- final step up: parent's increasing witness, accumulator for dec
          have hdirup : stepDir cur v = Dir.SWNE := if_pos hlt
          rw [hdirup]
          simp only [dirVec]
          refine ⟨⟨incc ++ [v], ?_, ?_, List.getLast?_concat, ?_⟩,
            ⟨dec ++ [v], ?_, ?_, List.getLast?_concat, ?_⟩, ?_, ?_⟩
          · exact pairwise_append_singleton hc1
              fun a ha => lt_of_le_of_lt (hccle a ha) hlt
          · have hsub : incc ++ [v] <+ l.take (idx + 1) := by
              rw [htakev]
              exact List.Sublist.append hc2' (List.Sublist.refl _)
            exact hsub
          · have hb : (cur.pos + ((1 : ℤ), (1 : ℤ))).1 +
                (cur.pos + ((1 : ℤ), (1 : ℤ))).2 + 2 ≤
                  2 * (((incc ++ [v]).length : ℕ) : ℤ) := by
              simp only [Prod.fst_add, Prod.snd_add, List.length_append,
                List.length_cons, List.length_nil]
              push_cast
              omega
            exact hb
          · exact pairwise_append_singleton hde1 fun a ha => hde3 a ha
          · have hsub : dec ++ [v] <+ l.take (idx + 1) := by
              rw [htakev]
              exact List.Sublist.append hde2 (List.Sublist.refl _)
            exact hsub
          · have hb : (cur.pos + ((1 : ℤ), (1 : ℤ))).1 -
                (cur.pos + ((1 : ℤ), (1 : ℤ))).2 + 2 ≤
                  2 * (((dec ++ [v]).length : ℕ) : ℤ) := by
              simp only [Prod.fst_add, Prod.snd_add, List.length_append,
                List.length_cons, List.length_nil]
              push_cast
              omega
            exact hb
          · have hb : (0 : ℤ) ≤ (cur.pos + ((1 : ℤ), (1 : ℤ))).1 +
                (cur.pos + ((1 : ℤ), (1 : ℤ))).2 := by
              simp only [Prod.fst_add, Prod.snd_add]
              omega
            exact hb
          · have hb : (0 : ℤ) ≤ (cur.pos + ((1 : ℤ), (1 : ℤ))).1 -
                (cur.pos + ((1 : ℤ), (1 : ℤ))).2 := by
              simp only [Prod.fst_add, Prod.snd_add]
              omega
            exact hb
        · -- final step down: accumulator for inc, parent's decreasing witness
          have hvlt := hvne hlt
          have hdirdown : stepDir cur v = Dir.NWSE := if_neg hlt
          rw [hdirdown]
          simp only [dirVec]
          refine ⟨⟨inc ++ [v], ?_, ?_, List.getLast?_concat, ?_⟩,
            ⟨decc ++ [v], ?_, ?_, List.getLast?_concat, ?_⟩, ?_, ?_⟩
          · exact pairwise_append_singleton hi1 fun a ha => hi3 a ha
          · have hsub : inc ++ [v] <+ l.take (idx + 1) := by
              rw [htakev]
              exact List.Sublist.append hi2 (List.Sublist.refl _)
            exact hsub
          · have hb : (cur.pos + ((1 : ℤ), (-1 : ℤ))).1 +
                (cur.pos + ((1 : ℤ), (-1 : ℤ))).2 + 2 ≤
                  2 * (((inc ++ [v]).length : ℕ) : ℤ) := by
              simp only [Prod.fst_add, Prod.snd_add, List.length_append,
                List.length_cons, List.length_nil]
              push_cast
              omega
            exact hb
          · exact pairwise_append_singleton hg1
              fun a ha => lt_of_lt_of_le hvlt (hgcge a ha)
          · have hsub : decc ++ [v] <+ l.take (idx + 1) := by
              rw [htakev]
              exact List.Sublist.append hg2' (List.Sublist.refl _)
            exact hsub
          · have hb : (cur.pos + ((1 : ℤ), (-1 : ℤ))).1 -
                (cur.pos + ((1 : ℤ), (-1 : ℤ))).2 + 2 ≤
                  2 * (((decc ++ [v]).length : ℕ) : ℤ) := by
              simp only [Prod.fst_add, Prod.snd_add, List.length_append,
                List.length_cons, List.length_nil]
              push_cast
              omega
            exact hb
          · have hb : (0 : ℤ) ≤ (cur.pos + ((1 : ℤ), (-1 : ℤ))).1 +
                (cur.pos + ((1 : ℤ), (-1 : ℤ))).2 := by
              simp only [Prod.fst_add, Prod.snd_add]
              omega
            exact hb
          · have hb : (0 : ℤ) ≤ (cur.pos + ((1 : ℤ), (-1 : ℤ))).1 -
                (cur.pos + ((1 : ℤ), (-1 : ℤ))).2 := by
              simp only [Prod.fst_add, Prod.snd_add]
              omega
            exact hb
    · -- walk through an occupied position
      have hfind' : G.nodes.find?
          (fun n => decide (n.pos = cur.pos + dirVec (stepDir cur v))) = some next :=
        hfind
      have hnext : next ∈ G.nodes := List.mem_of_find?_eq_some hfind'
      have hposn : next.pos = cur.pos + dirVec (stepDir cur v) := by
        have := List.find?_some hfind'
        simpa using this
      by_cases hlt : cur.val < v
      · have hdirup : stepDir cur v = Dir.SWNE := if_pos hlt
        refine ih G next incc dec hB hnext hm hc1 hc2' ?_ ?_ hde1 hde2 hde3 ?_
        · exact fun a ha => lt_of_le_of_lt (hccle a ha) hlt
        · rw [hposn, hdirup]
          simp only [dirVec, Prod.fst_add, Prod.snd_add]
          omega
        · rw [hposn, hdirup]
          simp only [dirVec, Prod.fst_add, Prod.snd_add]
          omega
      · have hvlt := hvne hlt
        have hdirdown : stepDir cur v = Dir.NWSE := if_neg hlt
        refine ih G next inc decc hB hnext hm hi1 hi2 hi3 ?_ hg1 hg2' ?_ ?_
        · rw [hposn, hdirdown]
          simp only [dirVec, Prod.fst_add, Prod.snd_add]
          omega
        · exact fun a ha => lt_of_lt_of_le hvlt (hgcge a ha)
        · rw [hposn, hdirdown]
          simp only [dirVec, Prod.fst_add, Prod.snd_add]
          omega

/-- The fold over the remaining elements preserves the monotone-witness
    invariant. -/
lemma build_loop_mono (l : List α) (hd : l.Nodup) (root : SGNode α)
    (hrpos : root.pos = (0, 0)) :
    ∀ (k b : ℕ) (G : SequenceGraph α), l.length - b ≤ k → b ≤ l.length →
      BuildInv l b G → root ∈ G.nodes → MonoInv l G →
      MonoInv l
        (((l.drop b).zipIdx b).foldl
          (fun G vi => insertElement root G vi.2 vi.1) G) := by
  intro k
  induction k with
  | zero =>
    intro b G hk hble h hroot hm
    have hdrop : l.drop b = [] := List.drop_eq_nil_of_le (by omega)
    rw [hdrop]
    exact hm
  | succ k ih =>
    intro b G hk hble h hroot hm
    by_cases hb : b < l.length
    · rw [List.drop_eq_getElem_cons hb, List.zipIdx_cons, List.foldl_cons]
      obtain ⟨t, ht⟩ := walkInsert_nodes_mono b l[b] (G.nodes.length + 1) G root
      refine ih (b + 1) _ (by omega) (by omega) ?_ ?_ ?_
      · exact walkInsert_inv hb (by simp) _ G root h hroot
      · change root ∈ (walkInsert b l[b] (G.nodes.length + 1) G root).nodes
        rw [ht]
        exact List.mem_append_left _ hroot
      · refine walkInsert_monoInv hd hb (by simp) _ G root [] [] h hroot hm
          List.Pairwise.nil (List.nil_sublist _) (by simp) ?_
          List.Pairwise.nil (List.nil_sublist _) (by simp) ?_
        · rw [hrpos]
          simp
        · rw [hrpos]
          simp
    · have hdrop : l.drop b = [] := List.drop_eq_nil_of_le (by omega)
      rw [hdrop]
      exact hm

/-- Every node of the constructed graph carries monotone witnesses. -/
lemma buildGraph_monoInv (l : List α) (hd : l.Nodup) : MonoInv l (buildGraph l) := by
  cases l with
  | nil =>
    intro n hn
    simp [buildGraph] at hn
  | cons x xs =>
    have hm0 : MonoInv (x :: xs) ⟨[⟨0, x, (0, 0)⟩], []⟩ := by
      intro n hn
      rw [List.mem_singleton] at hn
      subst hn
      refine ⟨⟨[x], List.pairwise_singleton _ _, by simp, rfl, by simp⟩,
        ⟨[x], List.pairwise_singleton _ _, by simp, rfl, by simp⟩, by simp, by simp⟩
    exact build_loop_mono (x :: xs) hd ⟨0, x, (0, 0)⟩ rfl (x :: xs).length 1
      ⟨[⟨0, x, (0, 0)⟩], []⟩ (by omega) (by simp) (buildInv_init x xs) (by simp) hm0

/-- **Lemmas 3 & 4.** Paths in the constructed graph witness monotonic
    subsequences.  In the paper this is the branch-splicing argument; here
    it falls out of the monotone-witness invariant `MonoInv` (see the
    blueprint above): the endpoint of a path with `k` northeast edges has
    `u`-coordinate at least `2k`, so its increasing witness has length at
    least `k + 1`. -/
lemma buildGraph_monotone (l : List α) (hd : l.Nodup) :
    ∀ p : SGPath (buildGraph l),
      (∃ sub : List α, p.neCount + 1 ≤ sub.length ∧
        StrictlyIncreasing sub ∧ sub <+ l) ∧
      (∃ sub : List α, p.seCount + 1 ≤ sub.length ∧
        StrictlyDecreasing sub ∧ sub <+ l) := by
  intro p
  have hane : p.path.nodes ≠ [] := p.nonempty
  have hha : p.path.nodes.head hane ∈ (buildGraph l).nodes :=
    p.nodes_subset _ (List.head_mem hane)
  have hhb : p.path.nodes.getLast hane ∈ (buildGraph l).nodes :=
    p.nodes_subset _ (List.getLast_mem hane)
  have hne : l ≠ [] := by
    intro h
    subst h
    simp [buildGraph] at hha
  have wf := buildGraph_wellFormed l hne
  have hm := buildGraph_monoInv l hd
  have hpos := p.getLast_pos wf
  obtain ⟨⟨incb, hb1, hb2, hb3, hb4⟩, ⟨decb, hg1, hg2, hg3, hg4⟩, _, _⟩ := hm _ hhb
  obtain ⟨_, _, hau, hav⟩ := hm _ hha
  have h1 := congrArg Prod.fst hpos
  have h2 := congrArg Prod.snd hpos
  simp only [Prod.fst_add, Prod.snd_add] at h1 h2
  constructor
  · refine ⟨incb, ?_, hb1, hb2.trans (List.take_sublist _ _)⟩
    push_cast at h1 h2
    omega
  · refine ⟨decb, ?_, hg1, hg2.trans (List.take_sublist _ _)⟩
    push_cast at h1 h2
    omega

/-- The construction delivers a `ConstructedGraph` for every nonempty
    duplicate-free list. -/
theorem exists_constructedGraph (l : List α) (hd : l.Nodup) (hne : l ≠ []) :
    Nonempty (ConstructedGraph l) :=
  ⟨{ G := buildGraph l
     wf := buildGraph_wellFormed l hne
     root := ⟨0, l.head hne, (0, 0)⟩
     rootpath := buildGraph_rootpath l hne
     no_overlap := buildGraph_noOverlap l
     complete := buildGraph_complete l
     monotone := buildGraph_monotone l hd }⟩

end Construction

/-! ## §10  Main theorems -/

section MainTheorems

/-- **Theorem 2.**  A sequence of length > n² with distinct elements has a
    monotonic subsequence of length ≥ n + 1. -/
theorem monotone_subseq_of_length_sq
    {l : List α} (hd : l.Nodup) (n : ℕ) (hlen : n ^ 2 < l.length) :
    ∃ sub : List α,
      n + 1 ≤ sub.length ∧ IsMonotonic sub ∧ sub <+ l := by
  have hne : l ≠ [] := by
    intro h
    rw [h] at hlen
    simp at hlen
  obtain ⟨CG⟩ := exists_constructedGraph l hd hne
  obtain ⟨p, hp⟩ := wide_path_of_many_nodes CG n (by rw [CG.complete]; exact hlen)
  rcases hp with h | h
  · obtain ⟨sub, hslen, hinc, hsub⟩ := (CG.monotone p).1
    exact ⟨sub, by omega, Or.inl hinc, hsub⟩
  · obtain ⟨sub, hslen, hdec, hsub⟩ := (CG.monotone p).2
    exact ⟨sub, by omega, Or.inr hdec, hsub⟩

/-- **Theorem 1.**  Every sequence of 101 distinct elements contains a
    monotonic subsequence of length at least 11. -/
theorem monotone_subseq_length_11
    (l : List α) (hd : l.Nodup) (hlen : l.length = 101) :
    ∃ sub : List α,
      11 ≤ sub.length ∧ IsMonotonic sub ∧ sub <+ l := by
  apply monotone_subseq_of_length_sq hd 10
  simp [hlen]

end MainTheorems
