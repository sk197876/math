(** Federer (1969), 2.2.10(2), p. 67: the displayed Borel set T equals f(C).
    Forward membership follows the source partition; reverse membership
    recovers compatible words and a point in the shrinking closed
    intersections. All trees are used through their abstract laws. Source
    editions: BorelImageTreeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import CompleteMetricUP ClosedCoverTreeUP ClosedCoverBranches
  CoverPartitionTreeUP CoverPartitionTreeBasic BorelImageTreeUP BorelImageTreeBasic
  ShrinkingClosedImageLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [cover_partition_level_membership]: supporting partition
    exhaustion in Federer 2.2.10(2), p. 67: every point belongs to one A(s)
    at each word length. Existence suffices here; sibling disjointness
    supplies uniqueness when recovering target branches. *)
Lemma cover_partition_level_membership (R : realType) (T : metricType R)
    (E A : seq nat -> set T) (hE : is_closed_cover_tree E)
    (hA : is_cover_partition_tree E A) x k :
  exists s, size s = k /\ A s x.
Proof.
elim: k=> [|k [s [hs hx]]].
- exists [::]; split=> //; by rewrite (cover_partition_root hA).
- rewrite (@cover_partition_children_cover R T E A hE hA s) in hx.
  have [j _ hj] := hx; exists (j::s); split=> //; by rewrite /= hs.
Qed.

(** Source for [borel_image_tree_image_subset]: first inclusion
    toward T=f(C) in Federer 2.2.10(2), p. 67: the
    partition pieces cover C at every level and their images
    lie in the corresponding Borel containers. *)
Lemma borel_image_tree_image_subset (R : realType) (T : metricType R)
    (Y : topologicalType) (f : T -> Y) (C : set T) (E A : seq nat -> set T)
    (B : seq nat -> set Y) (hE : is_closed_cover_tree E)
    (hA : is_cover_partition_tree E A) (hB : is_borel_image_tree f C E A B) :
  f @` C `<=` borel_image_tree_target B.
Proof.
move=> y [x hx <-] k _.
have [s [hs hxs]] := @cover_partition_level_membership R T E A hE hA x k.+1.
exists s=> //; apply: (@borel_image_tree_contains T Y f C E A B hB s).
exists x=> //; by split.
Qed.

(** Source for [borel_image_tree_target_subset]: final inclusion toward
    T=f(C) in Federer 2.2.10(2), p. 67. Compatible target words give nested
    closed subsets of C of vanishing diameter; continuity and Hausdorff
    separation identify the target point with the image of their common
    point. *)
Lemma borel_image_tree_target_subset (R : realType) (T : metricType R)
    (Y : topologicalType) (f : T -> Y) (C : set T) (E A : seq nat -> set T)
    (B : seq nat -> set Y) (hE : is_closed_cover_tree E)
    (hA : is_cover_partition_tree E A) (hB : is_borel_image_tree f C E A B) :
  is_complete_metric_space T -> hausdorff_space Y -> continuous f -> closed C ->
  borel_image_tree_target B `<=` f @` C.
Proof.
move=> hT hY hf hC y hy.
have [w [hw [hw0 hwS]]] := @borel_image_tree_compatible_words T Y f C E A B hB y hy.
pose F k := C `&` E (w k.+1).
have hne k : w k.+1 != [::] by rewrite -size_eq0 (hw k.+1).1.
have hclosed k : closed (F k).
  apply: closedI=> //; exact: (@closed_cover_tree_closed R T E hE (w k.+1)).
have hnested : forall n m, (n <= m)%N -> F m `<=` F n.
  apply: successive_set_inclusions_nested=> k x [hx hEx]; split=> //.
  rewrite (hwS k.+1) in hEx.
  exact: (@closed_cover_tree_child_subset R T E hE (w k.+1) (head 0%N (w k.+2)) x hEx).
have hsmall : forall e : R, 0 < e -> exists k, forall x z,
    F k x -> F k z -> mdist x z < e.
  move=> e he; have [k hk] := closed_cover_tree_scale_small he.
  exists k=> x z [_ hx] [_ hz].
  have hb := @closed_cover_tree_diameter R T E hE (w k.+1) (hne k) x z hx hz.
  rewrite (hw k.+1).1 in hb; exact: le_lt_trans hb hk.
have hycl k : closure (f @` F k) y.
  apply: (@borel_image_tree_closure_bound T Y f C E A B hB (w k.+1)).
  - by move=> he; move: (hne k); rewrite he eqxx.
  - exact: (hw k.+1).2.
have [x [hx hfx]] := @shrinking_closed_image_limit R T Y f F y
  hT hY hf hclosed hnested hsmall hycl.
exists x=> //; exact: (hx 0%N).1.
Qed.

(** Source for [borel_image_tree_target_eq]: direct equality T=f(C)
    completing the displayed-set argument in Federer 2.2.10(2), p. 67. *)
Theorem borel_image_tree_target_eq (R : realType) (T : metricType R)
    (Y : topologicalType) (f : T -> Y) (C : set T) (E A : seq nat -> set T)
    (B : seq nat -> set Y) (hE : is_closed_cover_tree E)
    (hA : is_cover_partition_tree E A) (hB : is_borel_image_tree f C E A B) :
  is_complete_metric_space T -> hausdorff_space Y -> continuous f -> closed C ->
  borel_image_tree_target B = f @` C.
Proof.
move=> hT hY hf hC; apply/seteqP; split.
- exact: (@borel_image_tree_target_subset R T Y f C E A B hE hA hB hT hY hf hC).
- exact: (@borel_image_tree_image_subset R T Y f C E A B hE hA hB).
Qed.
