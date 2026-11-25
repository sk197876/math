(** Federer (1969), 3.2.46, p. 281: use the actual segment
    retraction already introduced in 2.5.18(2), p. 112, to obtain a
    Lipschitz representative on the whole scalar line. The original
    curve is required to be Lipschitz only on its compact interval. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra
  classical_sets topology.
From Federer Require Import RealMetricBackground LipschitzUP StieltjesSubstitution.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_minimum_right_nonexpanding]: supporting
    contraction of the scalar retraction in 2.5.18(2), p. 112,
    used for the interval curves of 3.2.46, p. 281. *)
Lemma scalar_minimum_right_nonexpanding (R : realType) (x y b : R) :
  `|Order.min x b-Order.min y b| <= `|x-y|.
Proof.
change (`|Num.min x b-Num.min y b| <= `|x-y|).
case: (leP x b)=> hxb; case: (leP y b)=> hyb.
- by [].
- rewrite -(ler_sqr (normr_ge0 _) (normr_ge0 _)) -!normrX.
  rewrite !ger0_norm ?sqr_ge0 //; nra.
- rewrite -(ler_sqr (normr_ge0 _) (normr_ge0 _)) -!normrX.
  rewrite !ger0_norm ?sqr_ge0 //; nra.
- by rewrite subrr normr0 normr_ge0.
Qed.

(** Source for [scalar_maximum_left_nonexpanding]: supporting
    contraction of the scalar retraction in 2.5.18(2), p. 112,
    used for the interval curves of 3.2.46, p. 281. *)
Lemma scalar_maximum_left_nonexpanding (R : realType) (a x y : R) :
  `|Order.max a x-Order.max a y| <= `|x-y|.
Proof.
change (`|Num.max a x-Num.max a y| <= `|x-y|).
case: (leP a x)=> hax; case: (leP a y)=> hay.
- by [].
- rewrite -(ler_sqr (normr_ge0 _) (normr_ge0 _)) -!normrX.
  rewrite !ger0_norm ?sqr_ge0 //; nra.
- rewrite -(ler_sqr (normr_ge0 _) (normr_ge0 _)) -!normrX.
  rewrite !ger0_norm ?sqr_ge0 //; nra.
- by rewrite subrr normr0 normr_ge0.
Qed.

(** Source for [segment_retraction_nonexpanding]: the actual
    scalar retraction is nonexpanding, supporting localization of
    the Lipschitz curves in Federer 3.2.46, p. 281, via the same
    retraction as 2.5.18(2), p. 112. *)
Lemma segment_retraction_nonexpanding (R : realType) (a b x y : R) :
  `|segment_retraction a b x-segment_retraction a b y| <= `|x-y|.
Proof.
rewrite /segment_retraction.
exact: le_trans (scalar_maximum_left_nonexpanding _ _ _)
  (scalar_minimum_right_nonexpanding _ _ _).
Qed.

(** Source for [metric_curve_retraction_lipschitz]: interval-only
    Lipschitz curves in Federer 3.2.46, p. 281, admit a globally
    Lipschitz representative with the same bound. No regularity
    outside the original interval is imposed on the original curve. *)
Lemma metric_curve_retraction_lipschitz (R : realType) (Y : metricType R)
    (C : real_line_metric R -> Y) (a b L : R) :
  a <= b -> @is_metric_lipschitz_bound R
    [the metricType R of real_line_metric R] Y `[a,b] C L ->
  @is_metric_lipschitz_bound R [the metricType R of real_line_metric R] Y
    setT (fun t => C (segment_retraction a b t)) L.
Proof.
move=> hab [hL hC]; split=> // x y _ _.
have hx : (`[a,b] : set (real_line_metric R)) (segment_retraction a b x).
  by rewrite /= in_itv /=; exact: (@segment_retraction_bounds R a b x hab).
have hy : (`[a,b] : set (real_line_metric R)) (segment_retraction a b y).
  by rewrite /= in_itv /=; exact: (@segment_retraction_bounds R a b y hab).
have h := hC _ _ hx hy.
change (is_true (mdist (C (segment_retraction a b x)) (C (segment_retraction a b y)) <=
  L*`|segment_retraction a b x-segment_retraction a b y|)) in h.
change (is_true (mdist (C (segment_retraction a b x)) (C (segment_retraction a b y)) <= L*`|x-y|)).
exact: le_trans h (ler_wpM2l hL (segment_retraction_nonexpanding a b x y)).
Qed.

(** Source for [metric_curve_retraction_agreement]: the original
    compact-interval values, hence endpoints, are unchanged in the
    curve localization for Federer 3.2.46, p. 281. *)
Lemma metric_curve_retraction_agreement (R : realType) (Y : Type)
    (C : R -> Y) (a b t : R) :
  a <= t <= b -> C (segment_retraction a b t) = C t.
Proof. by move=> ht; rewrite (segment_retraction_id ht). Qed.

(** Source for [metric_curve_retraction_image]: the actual whole
    representative stays in A whenever the original compact-interval
    curve does, supporting Federer 3.2.46, p. 281. *)
Lemma metric_curve_retraction_image (R : realType) (Y : Type)
    (C : R -> Y) (A : set Y) (a b : R) :
  a <= b -> (forall t, a <= t <= b -> A (C t)) ->
  forall t, A (C (segment_retraction a b t)).
Proof.
move=> hab hA t; apply: hA; exact: segment_retraction_bounds t hab.
Qed.
