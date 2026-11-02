(** Federer (1969), 2.4.12, p. 87: sealed finite
    Borel approximants on a closed separable linear subspace. Source
    editions and proof role: SeparableFiniteApproximationUP.v. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import RealNormUP NormMetric ModuleQuotient MetricSubsetBackground
  SeparableFiniteApproximationUP SeparableFiniteApproximationConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type SeparableFiniteApproximationSignature.
(** Source for [value]: abstract finite approximants supporting
    Federer 2.4.12, p. 87, with no exposed construction. *)
Parameter value : forall (R : realType) (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
  (Z : subspace V) (D : set (metric_subset (fun x : real_norm_metric_space hN => Z x))),
  closed (fun x : real_norm_metric_space hN => Z x) -> countable D -> dense D ->
  nat -> real_norm_metric_space hN -> real_norm_metric_space hN.
(** Source for [laws]: finite-image, Borel, range, error and
    convergence laws supporting Federer 2.4.12, p. 87. *)
Parameter laws : forall (R : realType) (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
  (Z : subspace V) (D : set (metric_subset (fun x : real_norm_metric_space hN => Z x)))
  (hZ : closed (fun x : real_norm_metric_space hN => Z x)) (hc : countable D) (hd : dense D),
  @is_separable_finite_approximation R V N hN Z (@value R V N hN Z D hZ hc hd).
End SeparableFiniteApproximationSignature.
Module SeparableFiniteApproximation : SeparableFiniteApproximationSignature.
(** Source for [value]: private selection of the proved
    approximation witness supporting Federer 2.4.12, p. 87. *)
Definition value (R : realType) (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
  (Z : subspace V) (D : set (metric_subset (fun x : real_norm_metric_space hN => Z x)))
  (hZ : closed (fun x : real_norm_metric_space hN => Z x)) (hc : countable D) (hd : dense D) :=
  projT1 (cid (@separable_finite_approximation_exists R V N hN Z D hZ hc hd)).
(** Source for [laws]: the selected witness satisfies the
    exposed laws supporting Federer 2.4.12, p. 87. *)
Lemma laws (R : realType) (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
  (Z : subspace V) (D : set (metric_subset (fun x : real_norm_metric_space hN => Z x)))
  (hZ : closed (fun x : real_norm_metric_space hN => Z x)) (hc : countable D) (hd : dense D) :
  @is_separable_finite_approximation R V N hN Z (@value R V N hN Z D hZ hc hd).
Proof. exact: projT2 (cid (@separable_finite_approximation_exists R V N hN Z D hZ hc hd)). Qed.
End SeparableFiniteApproximation.
