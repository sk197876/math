(** Public pruning sequence supporting Federer (1969), 2.10.47, p. 205. Only
    the opaque laws are imported; the recursive choices are inaccessible.
    Source context: DyadicPruningUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  DyadicCubeGridUP DyadicCubeGrid DyadicPruningUP RefiningCoverContent MetricRealPowerCost
  MetricRealPowerMeasureUP DyadicPruningSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
(** Source for [dyadic_compact_pruning]: public compact
    sequence of 2.10.47, p. 205. *)
Definition dyadic_compact_pruning := @DyadicCompactPruning.value.

(** Source for [dyadic_compact_pruning_specification]: public
    initial-set, compactness, nesting and common-mass laws
    for the sequence of 2.10.47, p. 205. *)
Lemma dyadic_compact_pruning_specification (R : realType) n (a : R_n R n)
    (Q : forall j, dyadic_cube_indices n j -> set (inner_metric_space (@euclidean_inner_productP R n)))
    (c p : R)
    (gamma : nat -> set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R)
    (mu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R)
    (hQ : is_dyadic_cube_grid a Q)
    (hg : forall j, is_refining_cover_content (dyadic_cube_level Q) (metric_real_diameter_cost c p) j (gamma j))
    (hmu : is_metric_real_power_measure c p mu)
    (hn : (0<n)%N) (hc : (0<c)%R) (hp : (0<p)%R)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) (h : nat)
    (hA : compact A) (hroot : forall x, A x -> forall l, (a l<=x l<=a l+1)%R)
    (hlevels : forall (l : 'I_n) (t : R), mu (A `&` [set x | x l=t])=0) :
  is_dyadic_compact_pruning gamma h A (@dyadic_compact_pruning R n a Q c p gamma mu hQ hg hmu hn hc hp A h hA hroot hlevels).
Proof. exact: DyadicCompactPruning.laws. Qed.
