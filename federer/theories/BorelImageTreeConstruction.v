(** Federer (1969), 2.2.10(2), p. 67: private recursive choice of the Borel
    sets B(s). Dependent nodes carry exactly the Borel and containment
    invariants needed for the next step. Source context: BorelImageTreeUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals topology.
From Federer Require Import CompleteMetricUP ClosedCoverTreeUP CoverPartitionTreeUP
  TopologicalBorel BorelImageTreeUP BorelImageRefinement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section Construction.
Context (R : realType) (T : metricType R) (Y : topologicalType) (f : T -> Y).
Context (C : set T) (E A : seq nat -> set T).
Context (hE : is_closed_cover_tree E) (hA : is_cover_partition_tree E A).
Context (hT : is_complete_metric_space T)
  (hsep : exists H : set T, countable H /\ dense H)
  (hY : hausdorff_space Y) (hf : continuous f) (hC : closed C)
  (hinj : forall x y, C x -> C y -> f x = f y -> x = y).

(** Source for [borel_image_node]: private invariant at a word
    s in Federer 2.2.10(2), p. 67: B(s) is Borel
    and contains f(C intersect A(s)). *)
Definition borel_image_node s :=
  {V : set Y | borel_set V /\ (f @` (C `&` A s)) `<=` V}.

(** Source for [borel_image_root_node]: private root B(empty)=Y in Federer
    2.2.10(2), p. 67. the discrepancy is recorded in the abstract source
    header. *)
Definition borel_image_root_node : borel_image_node [::] :=
  exist _ setT (conj (open_borel_set (@openT Y)) (subsetT _)).

(** Source for [borel_image_node_children_exist]: private one-step
    existence for B(s,j) in Federer 2.2.10(2), p. 67,
    retaining all inductive invariants and the closure bound. *)
Lemma borel_image_node_children_exist s (v : borel_image_node s) :
  exists B : nat -> set Y,
    (forall j, borel_set (B j) /\ (f @` (C `&` A (j::s))) `<=` B j /\
      B j `<=` proj1_sig v /\ B j `<=` closure (f @` (C `&` E (j::s)))) /\
    forall i j, i <> j -> B i `&` B j = set0.
Proof.
exact: (@borel_image_child_refinement R T Y f C E A hE hA (proj1_sig v) s
  hT hsep hY hf hC hinj (proj2_sig v).1 (proj2_sig v).2).
Qed.

(** Source for [borel_image_node_children]: private selection of
    the proved family of child Borel containers for Federer
    2.2.10(2), p. 67. *)
Definition borel_image_node_children s (v : borel_image_node s) :=
  projT1 (cid (borel_image_node_children_exist v)).

(** Source for [borel_image_node_children_laws]: the selected
    child family has the required invariants and sibling disjointness
    for Federer 2.2.10(2), p. 67. *)
Lemma borel_image_node_children_laws s (v : borel_image_node s) :
  (forall j, borel_set (borel_image_node_children v j) /\
    (f @` (C `&` A (j::s))) `<=` borel_image_node_children v j /\
    borel_image_node_children v j `<=` proj1_sig v /\
    borel_image_node_children v j `<=` closure (f @` (C `&` E (j::s)))) /\
  forall i j, i <> j -> borel_image_node_children v i `&` borel_image_node_children v j = set0.
Proof. exact: projT2 (cid (borel_image_node_children_exist v)). Qed.

(** Source for [borel_image_child_node]: private dependent child
    node for the recursion in Federer 2.2.10(2), p. 67. *)
Definition borel_image_child_node s (v : borel_image_node s) j : borel_image_node (j::s) :=
  exist _ (borel_image_node_children v j)
    (conj ((borel_image_node_children_laws v).1 j).1
      ((borel_image_node_children_laws v).1 j).2.1).

(** Source for [borel_image_node_tree]: private recursive witness B(s) in
    Federer 2.2.10(2), p. 67. Each step uses only the already constructed
    parent node and a proved child refinement. *)
Fixpoint borel_image_node_tree (s : seq nat) : borel_image_node s :=
  match s as t return borel_image_node t with
  | [::] => borel_image_root_node
  | j::t => borel_image_child_node (borel_image_node_tree t) j
  end.

(** Source for [borel_image_tree_exists]: proved existence of the
    full Borel image tree in Federer 2.2.10(2), p. 67.
    The recursive choices are subsequently sealed, leaving only
    the Borel, containment, nesting and closure laws public. *)
Theorem borel_image_tree_exists : exists B, is_borel_image_tree f C E A B.
Proof.
exists (fun s => proj1_sig (borel_image_node_tree s)); constructor.
- by [].
- move=> s; exact: (proj2_sig (borel_image_node_tree s)).1.
- move=> s; exact: (proj2_sig (borel_image_node_tree s)).2.
- move=> s j; exact: ((borel_image_node_children_laws (borel_image_node_tree s)).1 j).2.2.1.
- move=> s i j hij; exact: (borel_image_node_children_laws (borel_image_node_tree s)).2 i j hij.
- move=> s; case: s=> [|j s] hn; first by exfalso; apply: hn.
  exact: ((borel_image_node_children_laws (borel_image_node_tree s)).1 j).2.2.2.
Qed.
End Construction.
