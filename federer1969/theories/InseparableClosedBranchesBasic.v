(** Federer (1969), 2.2.10(1), p. 67: shrinking-branch consequences of the
    abstract specification. These proofs use only branch laws; no private
    choices are unfolded. Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import CompleteMetricUP ClosedCoverTreeUP ClosedCoverBranches
  InseparableClosedBranchesUP ShrinkingImageSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inseparable_branches_left_shrinking]: supporting
    vanishing-diameter consequence for the left branch in Federer
    2.2.10(1), p. 67. The 2.2.8 geometric scale tends to zero. *)
Lemma inseparable_branches_left_shrinking (R : realType) (T : metricType R)
    (Y : topologicalType) (f : T -> Y) (C D : set T) (P Q : nat -> set T)
    (h : is_inseparable_closed_branches f C D P Q) e :
  0 < e -> exists n, forall x y, P n x -> P n y -> mdist x y < e.
Proof.
move=> he; have [k hk] := closed_cover_tree_scale_small he.
exists k.+2=> x y hx hy; apply: le_lt_trans _ hk.
exact: (@inseparable_branches_left_diameter R T Y f C D P Q h k.+1 x y hx hy).
Qed.

(** Source for [inseparable_branches_right_shrinking]: supporting
    vanishing-diameter consequence for the right branch in Federer
    2.2.10(1), p. 67, with the same geometric scale. *)
Lemma inseparable_branches_right_shrinking (R : realType) (T : metricType R)
    (Y : topologicalType) (f : T -> Y) (C D : set T) (P Q : nat -> set T)
    (h : is_inseparable_closed_branches f C D P Q) e :
  0 < e -> exists n, forall x y, Q n x -> Q n y -> mdist x y < e.
Proof.
move=> he; have [k hk] := closed_cover_tree_scale_small he.
exists k.+2=> x y hx hy; apply: le_lt_trans _ hk.
exact: (@inseparable_branches_right_diameter R T Y f C D P Q h k.+1 x y hx hy).
Qed.

(** Source for [inseparable_closed_branches_contradiction]: final
    contradiction in Federer 2.2.10(1), p. 67: disjoint initial images
    cannot admit inseparable shrinking closed branches in a complete source
    with a continuous map to a Hausdorff target. *)
Lemma inseparable_closed_branches_contradiction (R : realType) (T : metricType R)
    (Y : topologicalType) (f : T -> Y) (C D : set T) (P Q : nat -> set T) :
  is_complete_metric_space T -> hausdorff_space Y -> continuous f ->
  (f @` C) `&` (f @` D) = set0 ->
  is_inseparable_closed_branches f C D P Q -> False.
Proof.
move=> hT hY hf hdis h.
have hd0 : (f @` P 0%N) `&` (f @` Q 0%N) = set0.
  by rewrite (inseparable_branches_left_root h) (inseparable_branches_right_root h).
have [n hn] := @shrinking_closed_images_eventually_separated R T Y f P Q hT hY hf
  (inseparable_branches_left_nonempty h) (inseparable_branches_right_nonempty h)
  (inseparable_branches_left_closed h) (inseparable_branches_right_closed h)
  (inseparable_branches_left_nested h) (inseparable_branches_right_nested h)
  (@inseparable_branches_left_shrinking R T Y f C D P Q h)
  (@inseparable_branches_right_shrinking R T Y f C D P Q h) hd0.
exact: (@inseparable_branches_not_separated R T Y f C D P Q h n hn).
Qed.
