(** Federer (1969), 2.9.22, pp. 167–168: every scalar Lipschitz curve alpha
    o g is absolutely continuous, so its derivative integral is its endpoint
    increment by 2.9.20. These supporting lemmas prove the exact
    finite-family condition 2.9.20(3), p. 165. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground OrderedIntervalFamilyUP RealAbsoluteContinuityUP
  CurveArcLength LipschitzCurveVariation StieltjesImageMeasures RealAbsoluteContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lipschitz_real_interval_family_bound]: supporting
    finite-family bound for the Lipschitz scalarisations in Federer
    2.9.22, p. 167, using exactly the ordered families of
    2.9.20(3), p. 165. Zero cell widths are excluded by
    the printed family condition, while the empty family is included. *)
Lemma lipschitz_real_interval_family_bound (R : realType) (g : R -> R) (L : R) :
  (forall t u, `|g t-g u|<=L * `|t-u|) -> forall a b s,
  is_ordered_real_interval_family a b s ->
  real_interval_family_increment_sum g s<=L * real_interval_family_length s.
Proof.
move=> hg a b s; elim: s a=> [|[u v] rest ih] a.
  by move=> _; rewrite /real_interval_family_increment_sum /real_interval_family_length
    !big_nil mulr0.
move=> [hau [huv [hvb hs]]].
have hb := hg v u.
have hvu : 0<v-u by rewrite subr_gt0.
rewrite (ger0_norm (ltW hvu)) in hb.
have ht := ih _ hs.
rewrite /real_interval_family_increment_sum /real_interval_family_length !big_cons.
change (`|g v-g u|+real_interval_family_increment_sum g rest<=
  L * ((v-u)+real_interval_family_length rest)).
rewrite mulrDr; exact: lerD hb ht.
Qed.

(** Source for [lipschitz_real_curve_absolutely_continuous]:
    direct supporting absolute continuity of alpha o g in
    Federer 2.9.22, p. 168. For every epsilon use
    delta=epsilon/(L+1) in the exact condition 2.9.20(3),
    p. 165; the zero Lipschitz constant is included. *)
Lemma lipschitz_real_curve_absolutely_continuous (R : realType) (g : R -> R)
    (L a b : R) : 0<=L -> (forall t u, `|g t-g u|<=L * `|t-u|) ->
  is_absolutely_continuous_real_curve g a b.
Proof.
move=> hL hg e he.
have hL1 : 0<L+1 by lra.
have hd : 0<e/(L+1) by rewrite divr_gt0.
exists (e/(L+1)); split=> // s hs hlen.
have hb := lipschitz_real_interval_family_bound hg hs.
have ht := le_trans hb (ler_wpM2l hL hlen).
have hL' : L<=L+1 by lra.
have hh := ler_wpM2r (ltW hd) hL'.
have heq : (L+1) * (e/(L+1))=e by field; rewrite (gt_eqF hL1).
rewrite heq in hh; exact: le_trans ht hh.
Qed.

(** Source for [lipschitz_real_derivative_integral_increment]:
    direct scalar derivative-integral identity used in Federer
    2.9.22, pp. 167–168, by 2.9.20(1), p. 165.
    Local finite variation and absolute continuity are proved
    from the supplied Lipschitz bound, not assumed separately. *)
Theorem lipschitz_real_derivative_integral_increment (R : realType) (g : R -> R)
    (L a b : R) : 0<=L -> (forall t u, `|g t-g u|<=L * `|t-u|) -> a<b ->
  real_curve_indefinite_derivative_integral g a b.
Proof.
move=> hL hg hab.
have hf := @lipschitz_curve_locally_finite_variation R
  [the metricType R of real_line_metric R] g L hg.
have [psip [psim hp]] := @induced_measure_pair_exists R g hf.
have [h12 [h23 h34]] := @federer_2_9_20 R g psip psim a b hf hp hab.
have hAC := lipschitz_real_curve_absolutely_continuous a b hL hg.
exact: h12.2 (h23.2 hAC).
Qed.
