(** Federer (1969), 2.9.19, pp. 164–165: compare finite derivative values
    and the arc-length derivative. The limit laws below are derived directly
    from the epsilon specification. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology lra.
From Federer Require Import RealMetricBackground CurveArcLength RealCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [punctured_real_limit_absolute]: supporting absolute-value
    limit in Federer 2.9.19, pp. 164–165 The reverse triangle inequality
    transfers every punctured epsilon estimate to the absolute values. *)
Lemma punctured_real_limit_absolute (R : realType) (u : R -> R) (a : R) :
  punctured_real_limit u a -> punctured_real_limit (fun h => `|u h|) `|a|.
Proof.
move=> hu e he; have [d [hd hB]] := hu e he.
exists d; split=> // h hh.
exact: le_lt_trans (ler_dist_dist _ _) (hB h hh).
Qed.

(** Source for [punctured_real_limit_order]: supporting passage of
    inequalities to finite derivative limits in Federer 2.9.19, pp. 164–165
    Pointwise order at every nonzero increment passes to the two finite
    punctured limits. A common positive increment inside both cutoffs proves
    the assertion. *)
Lemma punctured_real_limit_order (R : realType) (u v : R -> R) (a b : R) :
  punctured_real_limit u a -> punctured_real_limit v b ->
  (forall h : R, h != 0 -> u h<=v h) -> a<=b.
Proof.
move=> hu hv horder; rewrite leNgt; apply/negP=> hba.
pose e := (a-b)/3.
have he : 0<e by rewrite /e divr_gt0 // ?subr_gt0 // ltr0n.
have [du [hdu hU]] := hu e he.
have [dv [hdv hV]] := hv e he.
pose h := Num.min du dv/2.
have hmin : 0<Num.min du dv by rewrite lt_min hdu hdv.
have hp : 0<h by rewrite /h divr_gt0 // ltr0n.
have hsmall : h<Num.min du dv by rewrite /h; lra.
have hmu : Num.min du dv<=du by rewrite ge_min lexx.
have hmv : Num.min du dv<=dv by rewrite ge_min lexx orbT.
have hhu : 0<`|h|<du.
  rewrite (ger0_norm (ltW hp)); apply/andP; split=> //; exact: lt_le_trans hsmall hmu.
have hhv : 0<`|h|<dv.
  rewrite (ger0_norm (ltW hp)); apply/andP; split=> //; exact: lt_le_trans hsmall hmv.
have hn : h != 0 by rewrite (gt_eqF hp).
have hc := horder h hn.
have hA := hU h hhu; have hB := hV h hhv.
move: hA hB; rewrite !ltr_norml=> /andP [hA1 hA2] /andP [hB1 hB2].
have hbad : a<a by rewrite /e in hA1 hA2 hB1 hB2; lra.
by rewrite ltxx in hbad.
Qed.

(** Source for [real_bv_derivative_variation_bound]: supporting lower
    inequality |g'(x)|<=s'(x) in Federer 2.9.19, pp. 164–165 Apply the
    distance/variation bound of 2.5.16 to each orientation of a nonzero
    increment, divide by its positive absolute width, and pass to the finite
    derivative limits. *)
Lemma real_bv_derivative_variation_bound (R : realType)
    (g : R -> real_line_metric R) (x v w : R) :
  curve_locally_finite_variation g -> has_real_curve_derivative g x v ->
  has_real_curve_derivative (arc_length g) x w -> `|v|<=w.
Proof.
move=> hg hG hS.
apply: (@punctured_real_limit_order R
  (fun h => `|(g (x+h)-g x)/h|)
  (fun h => (arc_length g (x+h)-arc_length g x)/h) `|v| w
  (punctured_real_limit_absolute hG) hS).
move=> h hn; case: (ltP 0 h)=> [hh|hh].
- have hx : x<=x+h by rewrite lerDl; exact: ltW hh.
  have hb := @arc_length_distance R [the metricType R of real_line_metric R] g hg x (x+h) hx.
  rewrite real_line_metric_distanceE distrC in hb.
  rewrite normrM normfV.
  rewrite (ger0_norm (ltW hh)).
  have hi : 0<=h^-1 by rewrite invr_ge0; exact: ltW hh.
  exact (ler_wpM2r hi hb).
- have hnonpos : h<=0 by lra.
  have hneg : 0< -h by rewrite oppr_gt0 lt_neqAle hn hnonpos.
  have hx : x+h<=x by lra.
  have hb := @arc_length_distance R [the metricType R of real_line_metric R] g hg (x+h) x hx.
  rewrite real_line_metric_distanceE in hb.
  have heq : (arc_length g (x+h)-arc_length g x)/h=
      (arc_length g x-arc_length g (x+h))/(-h).
    by symmetry; rewrite -opprB divrNN.
  rewrite heq normrM normfV.
  rewrite (ler0_norm hnonpos).
  have hi : 0<=(-h)^-1 by rewrite invr_ge0; exact: ltW hneg.
  exact (ler_wpM2r hi hb).
Qed.
