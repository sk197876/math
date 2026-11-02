(** Federer (1969), 2.8.8, p. 145: the positive two-sided s^(-n) phi B(a,s)
    estimate implies diametric regularity when it holds at r and (1+2 tau)r.
    This module proves the scalar comparison without constructing a measure
    or assuming a volume formula. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MetricClosedBalls DiametricRegularityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [has_ball_power_growth_bounds]: the displayed
    estimate in Federer 2.8.8, p. 145. The positive
    lower constant and positive radius are separate premises;
    s^(-n) is the inverse of the natural power. The supporting
    arithmetic also permits dimension zero. *)
Definition has_ball_power_growth_bounds (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (n : nat) (u v : R) (a : X) (s : R) :=
  u%:E <= ((s ^+ n)^-1)%:E * mu (metric_closed_ball a s) /\
    ((s ^+ n)^-1)%:E * mu (metric_closed_ball a s) <= v%:E.

(** Source for [ball_power_growth_bounds_scaled]: supporting
    removal of s^(-n) in Federer 2.8.8, p. 145.
    Positive s makes multiplication by s^n reversible even
    for extended measure values. *)
Lemma ball_power_growth_bounds_scaled (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (n : nat) (u v : R) (a : X) (s : R) :
  (0 < s)%R -> has_ball_power_growth_bounds mu n u v a s ->
  (u * s ^+ n)%:E <= mu (metric_closed_ball a s) /\
    mu (metric_closed_ball a s) <= (v * s ^+ n)%:E.
Proof.
move=> hs [hl hu].
have hp : (0 < s ^+ n)%R by rewrite exprn_gt0.
have hne : (s ^+ n != 0)%R by rewrite (gt_eqF hp).
have hpE : 0 <= (s ^+ n)%:E by rewrite lee_fin ltW.
have hlo := lee_wpmul2l hpE hl.
have hup := lee_wpmul2l hpE hu.
rewrite muleA -!EFinM mulfV // mul1e in hlo hup.
split; by rewrite mulrC.
Qed.

(** Source for [ball_power_growth_dilation_bound]: the
    sufficient growth estimate for diametric regularity in
    Federer 2.8.8, p. 145. If the normalized ball
    measures lie between u and v at both radii, then any
    lambda>(v c^n)/u gives phi B(a,c r)<lambda phi B(a,r).
    Finite positive phi B(a,r) is derived, not assumed. *)
Theorem ball_power_growth_dilation_bound (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu) (n : nat)
    (u v c lambda : R) (a : X) (r : R) :
  (0 < u)%R -> (0 < c)%R -> (0 < r)%R ->
  has_ball_power_growth_bounds mu n u v a r ->
  has_ball_power_growth_bounds mu n u v a (c*r)%R ->
  (v*c^+n/u < lambda)%R ->
  mu (metric_closed_ball a (c*r)%R) < lambda%:E * mu (metric_closed_ball a r).
Proof.
move=> hu hc hr hg hgc hlambda.
have hp : (0 < r ^+ n)%R by rewrite exprn_gt0.
have hcr : (0 < c*r)%R by rewrite mulr_gt0.
have [hlo hup] := @ball_power_growth_bounds_scaled R X mu n u v a r hr hg.
have [_ hupc] := @ball_power_growth_bounds_scaled R X mu n u v a (c*r)%R hcr hgc.
have hpos : 0 < mu (metric_closed_ball a r).
  apply: lt_le_trans _ hlo; rewrite lte_fin; by rewrite mulr_gt0.
have hfin : mu (metric_closed_ball a r) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm _)).
  exact: le_lt_trans hup (ltry _).
have hvprod : (0 <= v*r^+n)%R.
  have h := le_trans (measure_nonnegative hm _) hup; by rewrite lee_fin in h.
have hv : (0 <= v)%R.
  have h : (0*r^+n <= v*r^+n)%R by rewrite mul0r.
  by move: h; rewrite (ler_pM2r hp).
pose k := (v*c^+n/u)%R.
have hk : (0 <= k)%R.
  apply: divr_ge0; last exact: ltW hu.
  apply: mulr_ge0=> //; apply: exprn_ge0; exact: ltW hc.
have hkE : 0 <= k%:E by rewrite lee_fin.
have hune : u != 0%R by rewrite (gt_eqF hu).
have heq : (k*(u*r^+n) = v*(c*r)^+n)%R.
  by rewrite /k exprMn !mulrA divfK.
have hmul := lee_wpmul2l hkE hlo.
rewrite -EFinM heq in hmul.
have hle := le_trans hupc hmul.
have hrp : (0 < fine (mu (metric_closed_ball a r)))%R.
  by move: hpos; rewrite -(fineK hfin) lte_fin.
have hs : k%:E * mu (metric_closed_ball a r) < lambda%:E * mu (metric_closed_ball a r).
  rewrite -(fineK hfin) -!EFinM lte_fin (ltr_pM2r hrp).
  exact hlambda.
exact: le_lt_trans hle hs.
Qed.

(** Source for [ball_power_growth_diametric_regularity]: the
    sufficient criterion in Federer 2.8.8, p. 145,
    with an explicit factor lambda>(v(1+2 tau)^n)/u. Only
    the two radii specified in the book are tested. *)
Theorem ball_power_growth_diametric_regularity (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu) (F : set (set X))
    (n : nat) (u v tau lambda : R) :
  (0 < u)%R -> (1 < tau)%R -> (v*(1+2*tau)^+n/u < lambda)%R ->
  (forall a r, (0 < r)%R -> F (metric_closed_ball a r) ->
    has_ball_power_growth_bounds mu n u v a r /\
    has_ball_power_growth_bounds mu n u v a ((1+2*tau)*r)%R) ->
  is_diametrically_regular_ball_family mu F tau lambda.
Proof.
move=> hu ht hl hg a r hr hF.
have ht0 : (0 < tau)%R := lt_trans ltr01 ht.
have hc : (0 < 1+2*tau)%R.
  apply: addr_gt0; first exact: ltr01.
  by rewrite mulr_gt0 // ltr0n.
have [h1 h2] := hg a r hr hF.
exact (@ball_power_growth_dilation_bound R X mu hm n u v (1+2*tau)%R lambda a r
  hu hc hr h1 h2 hl).
Qed.
