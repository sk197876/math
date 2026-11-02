(** Scalar and metric estimates in Federer (1969), 2.8.11, pp. 147–148, for
    the two classes P_1 and P_2. The strict inequalities in the book are
    retained. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology lra.
From Federer Require Import DirectionalLimitationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [radial_projection_triangle_lower]: the first
    displayed distance estimate on p. 148 of Federer 2.8.11.
    In words, rho(x,c)>=rho(a,c)+rho(b,c)-rho(a,b).
    Supporting consequence of the triangle inequality and the
    radial equations of 2.8.9. *)
Lemma radial_projection_triangle_lower (R : realType) (X : metricType R)
    (a b c x : X) : is_radial_projection_configuration a b c x ->
  mdist a c + mdist b c - mdist a b <= mdist x c.
Proof.
move=> [_ [_ hx]].
have h := metric_triangle b x c; rewrite (metric_sym b x) hx in h.
lra.
Qed.

(** Source for [directional_near_scalar_estimate]: the estimate
    for j=1 in Federer 2.8.11, p. 148. In the notation
    C=rho(a,c), H=rho(b,c), D=rho(a,b), t=r/tau,
    the triangle inequality gives X>=C+H-D. This supporting
    scalar lemma yields X>eta C. *)
Lemma directional_near_scalar_estimate (R : realType) (eta C H D t X : R) :
  eta < 1 -> t < C -> t < H -> D <= (2-eta)*t -> C+H-D <= X ->
  eta*C < X.
Proof. move=> he hC hH hD hX; nra. Qed.

(** Source for [directional_far_scalar_estimate]: the estimate
    for j=2 in Federer 2.8.11, p. 148. Alpha=1/k,
    C=rho(a,c), H=rho(b,c), D=rho(a,b), and s,t are
    the radii at b,c. The conclusion is the strict separation
    required before dividing by the positive C. *)
Lemma directional_far_scalar_estimate (R : realType)
    (eta alpha tau C H D r s t X : R) :
  0 < C -> 1 < tau -> eta+alpha+tau*(tau-1) < 1 ->
  r < alpha*C -> t < tau*C -> t-tau*t < H-s ->
  D <= r+s -> C+H-D <= X -> eta*C < X.
Proof.
move=> hC ht hparam hr hrad hH hD hX.
have h1 : 0 < (tau-1)*(tau*C-t) by rewrite mulr_gt0 ?subr_gt0.
have h2 : 0 < (1-(eta+alpha+tau*(tau-1)))*C by rewrite mulr_gt0 ?subr_gt0.
nra.
Qed.

(** Source for [controlled_distance_above_lower_bound]: the
    bounds rho(b,c)>inf{s,t}>r/tau in Federer 2.8.11,
    p. 148. A common strict lower bound for the two radii
    is also a strict lower bound for the center distance. *)
Lemma controlled_distance_above_lower_bound (R : realType) (X : metricType R)
    (P : set (X*R)) (tau u : R) : is_controlled_ball_family tau P ->
  forall p q, P p -> P q -> p <> q -> u < p.2 -> u < q.2 ->
  u < mdist p.1 q.1.
Proof.
move=> hP p q hp hq hne hu hv.
have [[h _]|[h _]] := controlled_pair_alternative hP hp hq hne;
  [exact: lt_trans hu h|exact: lt_trans hv h].
Qed.

(** Source for [controlled_distance_above_radius_ratio]:
    rho(a,c)>t/tau in the j=2 case of Federer 2.8.11,
    p. 148. Positive radii and tau>1 give the estimate
    from either alternative in controlledness. *)
Lemma controlled_distance_above_radius_ratio (R : realType) (X : metricType R)
    (P : set (X*R)) (tau : R) : is_controlled_ball_family tau P ->
  forall p q, P p -> P q -> p <> q -> q.2/tau < mdist p.1 q.1.
Proof.
move=> hP p q hp hq hne.
have ht := controlled_factor_gt_one hP.
have ht0 : 0 < tau := lt_trans ltr01 ht.
have hq0 := controlled_positive_radii hP hq.
have hsmall : q.2/tau < q.2.
  rewrite ltr_pdivrMr // -{1}(mulr1 q.2) (ltr_pM2l hq0); exact ht.
have [[h hr]|[h _]] := controlled_pair_alternative hP hp hq hne.
- exact: lt_trans hr h.
- exact: lt_trans hsmall h.
Qed.

(** Source for [controlled_pair_far_difference]: the bound
    rho(b,c)-s>t-tau t in Federer 2.8.11, p. 148.
    This is obtained from either alternative for the distinct
    pairs (b,s),(c,t) of a tau-controlled family. *)
Lemma controlled_pair_far_difference (R : realType) (X : metricType R)
    (P : set (X*R)) (tau : R) : is_controlled_ball_family tau P ->
  forall p q, P p -> P q -> p <> q ->
    q.2-tau*q.2 < mdist p.1 q.1-p.2.
Proof.
move=> hP p q hp hq hne.
have ht := controlled_factor_gt_one hP.
have ht0 : 0 < tau := lt_trans ltr01 ht.
have hq0 := controlled_positive_radii hP hq.
have [[h hr]|[h hr]] := controlled_pair_alternative hP hp hq hne.
- have hneg : q.2-tau*q.2 < 0 by rewrite subr_lt0 -{1}(mul1r q.2) ltr_pM2r.
  have hpos : 0 < mdist p.1 q.1-p.2 by rewrite subr_gt0.
  exact: lt_trans hneg hpos.
- have hpt : p.2 < tau*q.2.
    by move: hr; rewrite ltr_pdivrMr // mulrC.
  exact: ltrB h hpt.
Qed.
