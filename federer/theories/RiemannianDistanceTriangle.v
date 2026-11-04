(** Federer (1969), 3.2.46, p. 281: the triangle
    inequality for the infimum of actual Lipschitz curve
    lengths. Use genuine concatenations and finite-error
    infimum approximation; infinite distances are retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric RiemannianTensorUP RiemannianCurveCost
  RiemannianCurveIntegralSplitting RiemannianAdmissibleConcatenation
  RiemannianDistanceUP RiemannianDistance RiemannianDistanceApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [riemannian_distance_triangle]: the triangle
    assertion in Federer 3.2.46, p. 281. Every curve is
    actually admissible and its length sum is proved; no
    minimizing curve, finite global distance or path-length
    axiom is assumed. *)
Theorem riemannian_distance_triangle (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) x y z :
  (@riemannian_distance R n A g x z <=
    @riemannian_distance R n A g x y + @riemannian_distance R n A g y z)%E.
Proof.
have hError (r s e : R) : (r+e/2)+(s+e/2)=r+s+e by lra.
have hXY0 := @riemannian_distance_nonnegative R n A g x y.
have hYZ0 := @riemannian_distance_nonnegative R n A g y z.
case hXY: (@riemannian_distance R n A g x y)=> [r| |] in hXY0 *.
- case hYZ: (@riemannian_distance R n A g y z)=> [s| |] in hYZ0 *.
  + apply/lee_addgt0Pr=> e he.
    have hHalf : (0 < e/2)%R by rewrite divr_gt0 // ltr0n.
    have [C [a [b [hC hNearC]]]] :=
      @riemannian_distance_finite_approximation R n A g x y r (e/2) hXY hHalf.
    have [D [c [d [hD hNearD]]]] :=
      @riemannian_distance_finite_approximation R n A g y z s (e/2) hYZ hHalf.
    have [E [u [v [hAd hCost]]]] :=
      @riemannian_admissible_curves_concatenation R n A g hg x y z C D a b c d hC hD.
    have hInf := riemannian_distance_curve_bound (riemannian_distance_laws A g x z) hAd.
    rewrite hCost in hInf.
    have hCReal := riemannian_admissible_curve_cost_finite_value hg hC.
    have hDReal := riemannian_admissible_curve_cost_finite_value hg hD.
    rewrite hCReal lte_fin in hNearC.
    rewrite hDReal lte_fin in hNearD.
    apply: le_trans hInf _; rewrite hCReal hDReal -!EFinD lee_fin.
    have hSum := ltW (ltrD hNearC hNearD).
    by rewrite hError in hSum.
  + by rewrite addey // leey.
  + by [].
- have hNotNeg : @riemannian_distance R n A g y z != -oo%E.
    apply/negP=> /eqP hBad; by rewrite hBad in hYZ0.
  by rewrite addye // leey.
- by [].
Qed.
