(** Federer (1969), 2.4.19, p. 91: finite-image approximations with values
    in the closed convex set C. These supporting laws use a fixed point of C
    in place of zero. Convexity is unnecessary for approximation itself. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import RealNormUP NormMetric MetricSubsetBackground ClosedSetFiniteApproximationUP
  ClosedSetFiniteApproximationConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module Type ClosedSetFiniteApproximationSignature.
(** Source for [value]: abstract C-valued approximants for Federer 2.4.19,
    p. 91 *)
Parameter value : forall (R : realType) (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
  (C : set (real_norm_metric_space hN)) (z : metric_subset C) (D : set (metric_subset C)),
  closed C -> countable D -> dense D -> nat -> real_norm_metric_space hN -> real_norm_metric_space hN.
(** Source for [laws]: the approximation specification supporting
    Federer 2.4.19, p. 91. *)
Parameter laws : forall (R : realType) (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
  (C : set (real_norm_metric_space hN)) (z : metric_subset C) (D : set (metric_subset C))
  (hC : closed C) (hc : countable D) (hd : dense D),
  is_closed_set_finite_approximation C (val z) (@value R V N hN C z D hC hc hd).
End ClosedSetFiniteApproximationSignature.
Module ClosedSetFiniteApproximation : ClosedSetFiniteApproximationSignature.
(** Source for [value]: private witness choice for the approximation
    in Federer 2.4.19, p. 91. *)
Definition value (R : realType) (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
  (C : set (real_norm_metric_space hN)) (z : metric_subset C) (D : set (metric_subset C))
  (hC : closed C) (hc : countable D) (hd : dense D) :=
  projT1 (cid (@closed_set_finite_approximation_exists R V N hN C z D hC hc hd)).
(** Source for [laws]: the selected witness proves the abstract laws
    supporting Federer 2.4.19, p. 91. *)
Lemma laws (R : realType) (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
  (C : set (real_norm_metric_space hN)) (z : metric_subset C) (D : set (metric_subset C))
  (hC : closed C) (hc : countable D) (hd : dense D) :
  is_closed_set_finite_approximation C (val z) (@value R V N hN C z D hC hc hd).
Proof. exact: projT2 (cid (@closed_set_finite_approximation_exists R V N hN C z D hC hc hd)). Qed.
End ClosedSetFiniteApproximation.
