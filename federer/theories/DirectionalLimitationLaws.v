(** Elementary consequences of Federer's original directional limitation
    definition, 2.8.9, pp. 145–146. Source conventions and editions:
    DirectionalLimitationUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import CoveringFamilyUP DirectionalLimitationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

(** Source for [extended_open_ball_real_radius]: supporting
    agreement of the radius convention in Federer 2.8.9,
    pp. 145–146, with U(a,r) in 2.8.1, p. 141. *)
Lemma extended_open_ball_real_radius (R : realType) (X : metricType R)
    (a : X) (r : R) : metric_extended_open_ball a r%:E = metric_open_ball a r.
Proof.
by apply/seteqP; split=> x; rewrite /metric_extended_open_ball /metric_open_ball /= lte_fin.
Qed.

(** Source for [extended_open_ball_infinite_radius]: xi is
    infinity in the normed-space example of Federer 2.8.9,
    p. 146. Every finite-distance point belongs to U(a,infinity). *)
Lemma extended_open_ball_infinite_radius (R : realType) (X : metricType R)
    (a : X) : metric_extended_open_ball a +oo%E = setT.
Proof.
apply/seteqP; split=> x hx; first exact Logic.I.
by rewrite /metric_extended_open_ball /= ltry.
Qed.

(** Source for [directional_separation_lower_threshold]:
    supporting monotonicity of the separation premise in
    Federer 2.8.9, p. 145. A larger required distance
    ratio implies each smaller one. *)
Lemma directional_separation_lower_threshold (R : realType) (X : metricType R)
    (a : X) (eta theta : R) (B : set X) :
  eta <= theta -> directionally_separated_from a theta B -> directionally_separated_from a eta B.
Proof.
move=> hle hs b c hb hc hbc x hx; exact: le_trans hle (hs b c hb hc hbc x hx).
Qed.

(** Source for [directional_limit_from_finite_cardinal_bound]:
    finite-target boundary of the cardinal condition in
    Federer 2.8.9, p. 145. Any target of cardinality
    at most zeta satisfies that condition, without additional
    geometric assumptions. The numerical bounds are retained. *)
Lemma directional_limit_from_finite_cardinal_bound (R : realType) (X : metricType R)
    (A : set X) (xi : \bar R) (eta : R) (zeta : nat) :
  (0 < xi)%E -> 0 < eta <= 1/3 -> (0 < zeta)%N ->
  A #<= [set: 'I_zeta] -> is_directionally_limited_at A xi eta zeta.
Proof.
move=> hx he hz hA; constructor=> // a ha B hB hs.
have hBA : B `<=` A by move=> x hxB; exact: (hB x hxB).1.1.
exact: card_le_trans (subset_card_le hBA) hA.
Qed.

(** Source for [directional_limit_subset]: restriction of the target in
    Federer 2.8.9, p. 145, directly from the printed condition. *)
Lemma directional_limit_subset (R : realType) (X : metricType R)
    (A C : set X) (xi : \bar R) (eta : R) (zeta : nat) :
  A `<=` C -> is_directionally_limited_at C xi eta zeta -> is_directionally_limited_at A xi eta zeta.
Proof.
move=> hAC hC; constructor.
- exact: directional_radius_positive hC.
- exact: directional_separation_range hC.
- exact: directional_cardinal_positive hC.
- move=> a ha B hB hs.
  apply: (@directional_cardinal_bound R X C xi eta zeta hC a (hAC a ha) B _ hs).
  move=> x hxB; have [[hx hball] hne] := hB x hxB.
  split=> //; split=> //; exact: hAC x hx.
Qed.

(** Source for [directional_separated_family_finite]: the
    finite bound on a separated B in Federer 2.8.9,
    p. 145, implies finiteness rather than requiring it
    as a premise. Supporting later cardinal estimates. *)
Lemma directional_separated_family_finite (R : realType) (X : metricType R)
    (A : set X) (xi : \bar R) (eta : R) (zeta : nat) :
  is_directionally_limited_at A xi eta zeta -> forall a,
  A a -> forall B, B `<=` (A `&` metric_extended_open_ball a xi) `\` [set a] ->
  directionally_separated_from a eta B -> finite_set B.
Proof.
move=> hA a ha B hB hs.
have hbound := @directional_cardinal_bound R X A xi eta zeta hA a ha B hB hs.
exact: card_le_finite hbound (@finite_finset _ (@setT 'I_zeta)).
Qed.
