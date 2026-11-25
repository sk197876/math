(** Federer (1969), 3.3.19, p. 302: independently
    specified circular-disc family recursion. Index zero is
    the auxiliary original unit disc; index j+1 is book G_(j+4).
    Separation, counts and measure assertions are conclusions. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals.
From Federer Require Import EuclideanInnerProduct InnerMetric FactorialDiscScalesSealed
  CircularDiscRefinement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope fset_scope.

(** Source for [is_circular_disc_tree]: the literal original
    G_4 and G_n recurrence, 3.3.19, p. 302. No final
    compactness, disjointness or measure property is assumed. *)
Record is_circular_disc_tree (R:realType)
    (H:nat->{fset inner_metric_space (@euclidean_inner_productP R 2)}):Prop:={
  (** Source for [circular_disc_tree_root]: auxiliary root
      B(0,1) of the original example, 3.3.19, p. 302. *)
  circular_disc_tree_root:H 0%N=[fset 0%R];
  (** Source for [circular_disc_tree_step]: replace each
      original parent by its original circular children,
      exactly as in 3.3.19, p. 302. *)
  circular_disc_tree_step:forall j,H j.+1=
    circular_disc_refinement (H j) (@FactorialDiscScales.radius R j) (j+4)%N
}.
