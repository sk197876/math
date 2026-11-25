(** Federer (1969), 3.2.46, p. 281: "Clearly rho is a
    symmetric function satisfying the triangle inequality".
    Symmetry follows here from actual curve reversal and its
    proved integral identity, using only the sealed infimum laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric RiemannianTensorUP RiemannianCurveCost RiemannianCurveReversal
  RiemannianDistanceUP RiemannianDistance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ereal_scope.

(** Source for [riemannian_distance_symmetric]: the symmetry
    assertion in Federer 3.2.46, p. 281. Infinite distances
    between disconnected components are included. No finite
    distance premise or curve-length axiom is added. *)
Theorem riemannian_distance_symmetric (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) x y :
  @riemannian_distance R n A g x y = @riemannian_distance R n A g y x.
Proof.
have hOne (u v : inner_metric_space (@euclidean_inner_productP R n)) :
    @riemannian_distance R n A g v u <= @riemannian_distance R n A g u v.
  apply: (riemannian_distance_greatest (riemannian_distance_laws A g u v)).
  move=> C a b hC.
  have hReverse := @riemannian_reversed_curve_admissible R n A u v C a b hC.
  have hBound := @riemannian_distance_curve_bound R n A g v u
    (@riemannian_distance R n A g v u) (riemannian_distance_laws A g v u)
    (fun t=>C (a+b-t)%R) a b hReverse.
  by rewrite (@riemannian_reversed_curve_cost R n A g hg u v C a b hC) in hBound.
apply/eqP; rewrite eq_le; apply/andP; split; [exact: hOne y x | exact: hOne x y].
Qed.
