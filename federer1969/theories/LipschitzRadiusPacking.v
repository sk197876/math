(** Federer (1969), 3.1.12, pp. 223–224:
    the overlap cardinal bound for disjoint balls with
    positive Lipschitz radii. The proof retains the
    printed gamma and unit-ball-volume cancellation. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals constructive_ereal topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerMetric RealMetricBackground
  LipschitzUP LipschitzRadiusOverlap EuclideanUniformBallPacking MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section VariableRadiusPacking.
Variable R : realType.
Variable m : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Variables U S : set X.
Variable h : X->R.
Variables lambda alpha beta : R.
Hypothesis hSU : S `<=` U.
Hypothesis hp : forall y, U y -> 0<h y.
Hypothesis hLip : is_metric_lipschitz_bound U (fun y=>(h y : real_line_metric R)) lambda.
Hypothesis ha : 0<alpha.
Hypothesis hb : 0<beta.
Hypothesis hla : lambda*alpha<1.
Hypothesis hlb : lambda*beta<1.
Hypothesis hdisjoint : forall s t, S s -> S t -> s!=t ->
  forall y, metric_closed_ball s (h s) y -> metric_closed_ball t (h t) y -> False.

(** Source for [lipschitz_radius_overlap_cardinality]:
    the cardinal estimate in Federer 3.1.12, pp. 223–224.
    The stated upper bound on the Lipschitz constant
    is expressed by its equivalent distance inequality.
    All finite-set and volume obligations are proved. *)
Theorem lipschitz_radius_overlap_cardinality x : U x ->
  finite_set (lipschitz_radius_overlap S h alpha beta x) /\
  ((#|` fset_set (lipschitz_radius_overlap S h alpha beta x)|)%:R : R)<=
    (lipschitz_radius_enclosing_factor lambda alpha beta)^+m*
      (1+lambda*beta)^+m/(1-lambda*alpha)^+m.
Proof.
move=> hx.
pose Sx := lipschitz_radius_overlap S h alpha beta x.
pose c := (1-lambda*alpha)/(1+lambda*beta).
pose gamma := lipschitz_radius_enclosing_factor lambda alpha beta.
have hnum : 0<1-lambda*alpha by rewrite subr_gt0.
have hden : 0<1+lambda*beta.
  have hh := mulr_ge0 hLip.1 (ltW hb); lra.
have hc : 0<c by rewrite /c divr_gt0.
have hdb : 0<1-lambda*beta by rewrite subr_gt0.
have hna : 0<1+lambda*alpha.
  have hh := mulr_ge0 hLip.1 (ltW ha); lra.
have hbeta : 0<beta+1 by have := hb; lra.
have hgamma : 0<gamma.
  rewrite /gamma /lipschitz_radius_enclosing_factor.
  have ht : 0<(beta+1)*(1+lambda*alpha)/(1-lambda*beta).
    by rewrite divr_gt0 // mulr_gt0.
  have := ha; lra.
have hcx : 0<c*h x by rewrite mulr_gt0 //; exact: @hp x hx.
have hHx : 0<=gamma*h x by apply: mulr_ge0; [exact: ltW hgamma|exact: ltW (@hp x hx)].
have hsmall s : Sx s -> c*h x<=h s.
  move=> hs; exact: (lipschitz_radius_overlap_radius_bounds hSU hp hLip ha hb hla hlb hx hs).1.
have hcontain s : Sx s -> metric_closed_ball s (h s) `<=` metric_closed_ball x (gamma*h x).
  exact: lipschitz_radius_overlap_ball_inclusion hSU hp hLip ha hb hla hlb hx.
have hdis s t : Sx s -> Sx t -> s!=t -> forall y,
    metric_closed_ball s (h s) y -> metric_closed_ball t (h t) y -> False.
  move=> hs ht; exact: (@hdisjoint s t hs.1 ht.1).
have hfin := @euclidean_uniform_ball_packing_finite R m Sx h x (c*h x)
  (gamma*h x) hcx hsmall hcontain hdis.
have hbound := @euclidean_uniform_ball_packing_bound R m Sx h x (c*h x)
  (gamma*h x) hcx hHx hsmall hcontain hdis.
split; first exact hfin.
have hxp : 0<(h x)^+m by exact: exprn_gt0 (@hp x hx).
have hcp : 0<c^+m by exact: exprn_gt0 hc.
rewrite !exprMn mulrA (ler_pM2r hxp) in hbound.
have hratio : ((#|` fset_set Sx|)%:R : R)<=(gamma/c)^+m.
  rewrite exprMn exprVn (@ler_pdivlMr R (c^+m) _ _ hcp) /c exprMn; exact hbound.
have hid : (gamma/c)^+m=gamma^+m*(1+lambda*beta)^+m/(1-lambda*alpha)^+m.
  by rewrite /c invfM invrK !exprMn exprVn; ring.
by rewrite hid in hratio.
Qed.

(** Source for [federer_3_1_12_indexed]: both conclusions of
    Federer 3.1.12, pp. 223–224: ratios of
    neighboring radii and the finite overlap cardinal bound.
    The containing-ball step uses the correction on
    erratum p. 4, book p. 224 line 4. *)
Theorem federer_3_1_12_indexed x : U x ->
  (forall s, lipschitz_radius_overlap S h alpha beta x s ->
    (1-lambda*beta)/(1+lambda*alpha)<=h x/h s /\
      h x/h s<=(1+lambda*beta)/(1-lambda*alpha)) /\
  finite_set (lipschitz_radius_overlap S h alpha beta x) /\
  ((#|` fset_set (lipschitz_radius_overlap S h alpha beta x)|)%:R : R)<=
    (lipschitz_radius_enclosing_factor lambda alpha beta)^+m*
      (1+lambda*beta)^+m/(1-lambda*alpha)^+m.
Proof.
move=> hx; split.
- move=>s hs; exact (lipschitz_radius_overlap_ratios hSU hp hLip ha hb hla hlb hx hs).
- exact: lipschitz_radius_overlap_cardinality hx.
Qed.
End VariableRadiusPacking.
