(** Federer (1969), 3.2.46, printed p. 281: independent order laws
    specifying the distance as the infimum of actual curve costs.
    Across components the extended infimum can be infinite. No metric,
    local comparison or finite-distance theorem is assumed here. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric RealMetricBackground RiemannianCurveCost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_riemannian_curve_distance]: the infimum defining
    rho(x,y) in Federer 3.2.46, p. 281, expressed by independent
    lower-bound and greatest-lower-bound laws. *)
Record is_riemannian_curve_distance (R : realType) n
    (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (g : R_n R n -> R_n R n -> R_n R n -> R) x y (d : \bar R) : Prop := {
  (** Source for [riemannian_distance_curve_bound]: rho is below
      every admissible curve length, Federer 3.2.46, p. 281. *)
  riemannian_distance_curve_bound : forall C a b,
    is_riemannian_admissible_curve A x y C a b ->
    d <= riemannian_curve_cost g C a b;
  (** Source for [riemannian_distance_greatest]: rho is the greatest
      common lower bound of those lengths, Federer 3.2.46, p. 281. *)
  riemannian_distance_greatest : forall c : \bar R,
    (forall C a b, is_riemannian_admissible_curve A x y C a b ->
      c <= riemannian_curve_cost g C a b) -> c <= d
}.

(** Source for [riemannian_curve_distance_unique]: uniqueness of
    the infimum defining rho, Federer 3.2.46, p. 281. *)
Lemma riemannian_curve_distance_unique (R : realType) n A g x y d e :
  @is_riemannian_curve_distance R n A g x y d ->
  is_riemannian_curve_distance A g x y e -> d = e.
Proof.
move=> hd he; apply/eqP; rewrite eq_le; apply/andP; split.
- exact: (riemannian_distance_greatest he (riemannian_distance_curve_bound hd)).
- exact: (riemannian_distance_greatest hd (riemannian_distance_curve_bound he)).
Qed.
