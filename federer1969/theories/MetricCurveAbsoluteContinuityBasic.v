(** Federer (1969), 2.9.22, pp. 167–168: metric consequences of the extended
    finite-family condition 2.9.20(3), p. 165, and its relative continuity
    implication on p. 166. These supporting laws do not require derivative
    existence, completeness or reflexivity. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology lra.
From Federer Require Import MetricCurveAbsoluteContinuityUP OrderedIntervalFamilyUP
  RealAbsoluteContinuityUP RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_real_family_increment_sum]: supporting
    agreement of the metric condition in Federer 2.9.22,
    pp. 167–168, with the original scalar sum in 2.9.20(3),
    p. 165. Absolute-value symmetry identifies the two orientations. *)
Lemma metric_real_family_increment_sum (R : realType) (g : R -> R) (s : seq (R * R)) :
  metric_interval_family_increment_sum (g : R -> real_line_metric R) s=
    real_interval_family_increment_sum g s.
Proof.
rewrite /metric_interval_family_increment_sum /real_interval_family_increment_sum.
apply: eq_bigr=> [[u v] _]; by rewrite real_line_metric_distanceE distrC.
Qed.

(** Source for [metric_absolute_continuity_real_agreement]: supporting
    consistency for Federer 2.9.22, pp. 167–168. The metric law
    on the real line is exactly condition (3) of 2.9.20, p. 165,
    with the same strict cells and non-strict total bounds. *)
Lemma metric_absolute_continuity_real_agreement (R : realType) (g : R -> R) (a b : R) :
  is_absolutely_continuous_metric_curve (g : R -> real_line_metric R) a b <->
  is_absolutely_continuous_real_curve g a b.
Proof.
split=> hg e he; have [d [hd hb]] := hg e he; exists d; split=> // s hs hlen.
- have h := hb s hs hlen; by rewrite metric_real_family_increment_sum in h.
- rewrite metric_real_family_increment_sum; exact: hb.
Qed.

(** Source for [metric_family_lipschitz_postcomposition_bound]:
    supporting scalar dual estimate for Federer 2.9.22, p. 167.
    A Lipschitz map bounds the sum of endpoint distances by its
    constant times the original family cost, including an empty family. *)
Lemma metric_family_lipschitz_postcomposition_bound (R : realType) (X Y : metricType R)
    (f : X -> Y) (g : R -> X) (L : R) : 0<=L ->
  (forall x y, mdist (f x) (f y)<=L*mdist x y) -> forall s,
  metric_interval_family_increment_sum (fun t => f (g t)) s<=
    L*metric_interval_family_increment_sum g s.
Proof.
move=> hL hf; elim=> [|[u v] s ih].
- by rewrite /metric_interval_family_increment_sum !big_nil mulr0.
- rewrite /metric_interval_family_increment_sum !big_cons mulrDr.
  exact: lerD (hf _ _) ih.
Qed.

(** Source for [metric_absolute_continuity_lipschitz_postcomposition]:
    supporting scalarisation in Federer 2.9.22, p. 167, for the
    extension of 2.9.20(3), p. 165. Use epsilon/(L+1), retaining
    the zero Lipschitz bound without dividing by L. *)
Theorem metric_absolute_continuity_lipschitz_postcomposition (R : realType) (X Y : metricType R)
    (f : X -> Y) (g : R -> X) (L a b : R) : 0<=L ->
  (forall x y, mdist (f x) (f y)<=L*mdist x y) ->
  is_absolutely_continuous_metric_curve g a b ->
  is_absolutely_continuous_metric_curve (fun t => f (g t)) a b.
Proof.
move=> hL hf hg e he.
have hpos : 0<L+1 by lra.
have hep : 0<e/(L+1) by rewrite divr_gt0.
have [d [hd hb]] := hg (e/(L+1)) hep.
exists d; split=> // s hs hlen.
have hcost := @metric_family_lipschitz_postcomposition_bound R X Y f g L hL hf s.
have hsmall := ler_wpM2l hL (hb s hs hlen).
have hlast : L*(e/(L+1))<=e.
  rewrite mulrA ler_pdivrMr // mulrDr mulr1 [L*e]mulrC lerDl.
  exact: ltW he.
exact: le_trans hcost (le_trans hsmall hlast).
Qed.

(** Source for [metric_absolute_continuity_increment_control]:
    supporting single-cell estimate in Federer 2.9.22,
    pp. 167–168, extending the continuity step of 2.9.20,
    p. 166. Both endpoint orientations and equality are included,
    while eligible finite families retain strict cells. *)
Lemma metric_absolute_continuity_increment_control (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) : is_absolutely_continuous_metric_curve g a b ->
  forall e : R, 0<e -> exists d : R, 0<d /\ forall x y : R,
    a<=x -> x<=b -> a<=y -> y<=b -> `|y-x|<=d -> mdist (g x) (g y)<=e.
Proof.
move=> hg e he; have [d [hd hs]] := hg e he.
exists d; split=> // x y hax hxb hay hyb hxy.
case: (ltgtP x y)=> horder.
- have hf : is_ordered_real_interval_family a b [:: (x,y)] by [].
  have hlen : real_interval_family_length [:: (x,y)]<=d.
    by move: hxy; rewrite ger0_norm ?subr_ge0 ?(ltW horder) // /real_interval_family_length big_seq1.
  have := hs _ hf hlen; by rewrite /metric_interval_family_increment_sum big_seq1.
- have hf : is_ordered_real_interval_family a b [:: (y,x)] by [].
  have hlen : real_interval_family_length [:: (y,x)]<=d.
    move: hxy; rewrite distrC /real_interval_family_length big_seq1.
    by rewrite ger0_norm ?subr_ge0 ?(ltW horder).
  have := hs _ hf hlen; by rewrite /metric_interval_family_increment_sum big_seq1 metric_sym.
- by rewrite horder mdistxx; exact: ltW he.
Qed.

(** Source for [metric_absolute_continuity_continuous]: direct
    metric continuity consequence extended by Federer 2.9.22,
    pp. 167–168, from 2.9.20(3)=>(4), p. 166. Continuity is
    relative to the closed source segment; no global continuity at
    its endpoints or bounded-variation premise is imposed. *)
Theorem metric_absolute_continuity_continuous (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) : is_absolutely_continuous_metric_curve g a b ->
  {within (`[a,b] : set (real_line_metric R)), continuous (g : real_line_metric R -> Y)}.
Proof.
move=> hg; apply/subspace_continuousP=> x hx W hW.
have [e he hBall] := (metricType_numDomainType.nbhs_mdistP (g x) W).1 hW.
have he2 : 0<e/2 by rewrite divr_gt0 // ltr0n.
have [d [hd hcontrol]] := metric_absolute_continuity_increment_control hg he2.
change (nbhs (x : real_line_metric R) [set y | `[a,b] y -> W (g y)]).
apply: (filterS _ (nbhsx_ballx (x : real_line_metric R) d hd))=> y hy hyA.
move: hx hyA; rewrite /= !in_itv /= => /andP[hax hxb] /andP[hay hyb].
have hxy : `|y-x|<=d by apply: ltW; move: hy; rewrite /ball /= distrC.
apply: hBall; apply: le_lt_trans (hcontrol x y hax hxb hay hyb hxy) _.
by rewrite ltr_pdivrMr ?ltr0n // mulr_natr ltrDl.
Qed.

(** Source for [constant_metric_curve_absolutely_continuous]: zero
    family-cost boundary case of Federer 2.9.22, pp. 167–168,
    extending 2.9.20(3), p. 165. Constants satisfy the abstract
    law on every segment in an arbitrary metric target. *)
Lemma constant_metric_curve_absolutely_continuous (R : realType) (Y : metricType R)
    (c : Y) (a b : R) : is_absolutely_continuous_metric_curve (fun _ : R => c) a b.
Proof.
move=> e he; exists 1; split; first exact: ltr01.
move=> s hs hlen; rewrite /metric_interval_family_increment_sum mdistxx big1 //.
exact: ltW he.
Qed.
