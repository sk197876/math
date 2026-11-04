(** Federer (1969), 3.2.46, p. 282: local coordinate
    representatives can be extended without leaving a small
    closed ball inside the target chart. This supporting
    existence result combines the sealed extension of 2.10.43,
    p. 201, with actual nearest-point contraction from
    1.7.13, p. 37. All auxiliary maps remain existential. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  MetricClosedBalls LipschitzUP KirszbraunExtensionUP KirszbraunExtension
  EuclideanClosedBallRetraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_ball_lipschitz_extension_exists]:
    a Lipschitz map whose original image lies in a closed
    Euclidean ball has a same-bound global extension taking
    values in that same ball, supporting 3.2.46, p. 282,
    by 2.10.43, p. 201, and the proved ball retraction.
    Empty sources, zero Lipschitz bounds and zero radii are
    retained; no target injectivity is assumed or claimed. *)
Theorem euclidean_ball_lipschitz_extension_exists (R : realType) m n
    (S : set (inner_metric_space (@euclidean_inner_productP R m)))
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n))
    (L : R) (b : inner_metric_space (@euclidean_inner_productP R n)) (r : R) :
  0<=r -> is_metric_lipschitz_bound S f L ->
  (forall x, S x -> metric_closed_ball b r (f x)) ->
  exists F : inner_metric_space (@euclidean_inner_productP R m) ->
    inner_metric_space (@euclidean_inner_productP R n),
    (forall x, S x -> F x=f x) /\
    is_metric_lipschitz_bound setT F L /\
    forall x, metric_closed_ball b r (F x).
Proof.
move=> hr hLip hRange.
have [P [hPRange [hPFixed hPBound]]] := @euclidean_closed_ball_retraction_exists R n b r hr.
pose G := @euclidean_lipschitz_extension R m n S f L hLip.
have hG := @euclidean_lipschitz_extension_specification R m n S f L hLip.
exists (fun x=>P (G x)); split.
- move=> x hx; rewrite (@kirszbraun_extension_agreement_law R m n S f G L hG x hx).
  exact: hPFixed (hRange x hx).
- split; last by move=> x; exact: hPRange.
  split; first exact hLip.1.
  move=> x y _ _.
  have hP := hPBound.2 (G x) (G y) Logic.I Logic.I; rewrite mul1r in hP.
  exact: le_trans hP ((kirszbraun_extension_bound_law hG).2 x y Logic.I Logic.I).
Qed.

(** Source for [euclidean_chart_lipschitz_extension_exists]:
    an actual closed target ball contained in the original
    chart yields a global coordinate extension staying inside
    that chart, supporting localization in 3.2.46, p. 282.
    The containment and original-image premises are geometric
    ball conditions; no area, Jacobian or coarea law is assumed. *)
Corollary euclidean_chart_lipschitz_extension_exists (R : realType) m n
    (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (S : set (inner_metric_space (@euclidean_inner_productP R m)))
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n))
    (L : R) (b : inner_metric_space (@euclidean_inner_productP R n)) (r : R) :
  0<=r -> metric_closed_ball b r `<=` A -> is_metric_lipschitz_bound S f L ->
  (forall x, S x -> metric_closed_ball b r (f x)) ->
  exists F : inner_metric_space (@euclidean_inner_productP R m) ->
    inner_metric_space (@euclidean_inner_productP R n),
    (forall x, S x -> F x=f x) /\
    is_metric_lipschitz_bound setT F L /\ forall x, A (F x).
Proof.
move=> hr hBall hLip hRange.
have [F [hAgree [hBound hImage]]] := @euclidean_ball_lipschitz_extension_exists R m n S f L b r hr hLip hRange.
exists F; split; first exact hAgree; split; first exact hBound.
move=> x; exact: hBall (F x) (hImage x).
Qed.
