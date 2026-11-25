(** Federer (1969), 3.3.19, p. 302: private recursive
    existence of the original circular-disc families. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals.
From Federer Require Import EuclideanInnerProduct InnerMetric FactorialDiscScalesSealed
  CircularDiscRefinement CircularDiscTreeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope fset_scope.

(** Source for [circular_disc_recursive_centres]: private
    recursive witness for the original G_n, 3.3.19, p. 302. *)
Fixpoint circular_disc_recursive_centres (R:realType) (j:nat):
    {fset inner_metric_space (@euclidean_inner_productP R 2)}:=
  if j is k.+1 then circular_disc_refinement (circular_disc_recursive_centres R k)
    (@FactorialDiscScales.radius R k) (k+4)%N else [fset 0%R].

(** Source for [circular_disc_tree_exists]: existence of
    the original circular family recursion of 3.3.19,
    p. 302, before sealing the family. *)
Theorem circular_disc_tree_exists (R:realType):exists H,@is_circular_disc_tree R H.
Proof. exists (@circular_disc_recursive_centres R);by constructor. Qed.
