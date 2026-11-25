(** Federer (1969), 2.9.22, pp. 167–168: extend the variation conclusion of
    2.9.19, p. 165, to normed curves. A strictly larger arc-length
    derivative places the point in a metric variation-defect locus. the norm
    triangle inequality replaces its absolute-value triangle inequality. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology lra ring.
From Federer Require Import RealNormUP NormMetric CurveArcLength RealCurveDerivativeUP
  NormedCurveDerivativeUP RealDerivativeIncrementBounds NormedDerivativeIntervalError
  MetricVariationDefect ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [normed_excess_arc_derivative_in_defect_locus]: supporting
    normed extension in Federer 2.9.22, pp. 167–168, of the inclusion into
    the C_m sets in 2.9.19, p. 165 Two interval errors of size one fourth of
    the derivative gap leave at least half that gap in the metric variation
    defect. A reciprocal natural cutoff supplies the printed positive index. *)
Lemma normed_excess_arc_derivative_in_defect_locus (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N)
    (g : R -> real_norm_metric_space hN) (x w : R) (v : E) :
  has_normed_curve_derivative N g x v ->
  has_real_curve_derivative (arc_length g) x w -> N v<w ->
  exists n : nat, metric_variation_defect_locus g n x.
Proof.
move=> hG hS hgap.
pose gap := w-N v.
have hgap0 : 0<gap by rewrite /gap subr_gt0.
pose gamma := gap/4.
have hgamma : 0<gamma by rewrite /gamma divr_gt0 // ltr0n.
have [ds [hds hSB]] := @real_derivative_interval_bounds R (arc_length g) x w gamma hS hgamma.
have [dg [hdg hGE]] := @normed_derivative_interval_error R E N hN g x gamma v hG hgamma.
pose cutoff := Num.min (Num.min ds dg) (gap/2).
have hcutoff : 0<cutoff by rewrite /cutoff !lt_min hds hdg divr_gt0 // ltr0n.
have [n hn] := positive_reciprocal_nat_small hcutoff.
pose r := ((n.+1)%:R : R)^-1.
have hcs : cutoff<=ds by rewrite /cutoff ge_min ge_min lexx.
have hcg : cutoff<=dg by rewrite /cutoff ge_min ge_min lexx orbT.
have hcGap : cutoff<=gap/2 by rewrite /cutoff ge_min lexx orbT.
have hrs : r<ds := lt_le_trans hn hcs.
have hrg : r<dg := lt_le_trans hn hcg.
have hrGap : r<gap/2 := lt_le_trans hn hcGap.
exists n; move=> a b haxb /andP [hw hwr].
have hws : 0<b-a<ds by apply/andP; split=> //; exact: lt_trans hwr hrs.
have hwg : 0<b-a<dg by apply/andP; split=> //; exact: lt_trans hwr hrg.
have hSlo := (hSB a b haxb hws).1.
have hGerr := hGE a b haxb hwg.
have hnorm := real_seminorm_triangle hN.1 (g b-g a-(b-a) *: v) ((b-a) *: v).
rewrite subrK (real_seminorm_scale hN.1) (ger0_norm (ltW hw)) in hnorm.
have hGup := le_trans hnorm (lerD hGerr (lexx _)).
rewrite [N (g b-g a)](real_seminorm_subtract hN.1) [(b-a)*N v]mulrC in hGup.
have hdef := lerB hSlo hGup.
have heq : (w-gamma)*(b-a)-(gamma*(b-a)+N v*(b-a))=(gap/2)*(b-a).
  by rewrite /gamma /gap; field.
rewrite heq in hdef.
have hstrict : r*(b-a)<(gap/2)*(b-a) by rewrite (ltr_pM2r hw).
have hfinal := lt_le_trans hstrict hdef.
change ((b-a)/(n.+1)%:R<metric_variation_defect g a b).
rewrite /metric_variation_defect real_norm_metric_distanceE mulrC.
exact hfinal.
Qed.
