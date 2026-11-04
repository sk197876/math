(** Federer (1969), 3.2.46, p. 281: initial distance laws proved
    from genuine curves and the opaque infimum interface. Finite
    component metrics and local comparisons are separate theorems. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric RiemannianTensorUP RiemannianCurveCost RiemannianCurveConstant
  RiemannianDistanceUP RiemannianDistance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [riemannian_distance_self]: rho(x,x)=0 for x in A,
    supporting the metric claim in Federer 3.2.46, p. 281. The
    actual constant derivative and integral discharge the upper bound. *)
Lemma riemannian_distance_self (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) x (hx : A x) :
  @riemannian_distance R n A g x x = 0.
Proof.
apply/eqP; rewrite eq_le riemannian_distance_nonnegative andbT.
have h := @riemannian_distance_curve_bound R n A g x x
  (@riemannian_distance R n A g x x) (riemannian_distance_laws A g x x)
  (fun _ => x) 0%R 1%R (riemannian_constant_curve_admissible hx).
by rewrite (riemannian_constant_curve_cost hg hx) in h.
Qed.
