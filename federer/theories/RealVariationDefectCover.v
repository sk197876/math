(** Federer (1969), 2.9.19, p. 165: every point where s'>|g'| lies in some
    C_m. We select one reciprocal natural cutoff smaller than both
    derivative cutoffs and half the positive derivative gap. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology lra ring.
From Federer Require Import RealMetricBackground CurveArcLength RealCurveDerivativeUP
  RealDerivativeIncrementBounds RealVariationDefectUP ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [excess_arc_derivative_in_defect_locus]: direct inclusion
    {x:s'(x)>|g'(x)|} in the union of C_m in Federer 2.9.19, p. 165 With
    gap=w-|v|, two interval errors of size gap/4 leave defect at least
    half-gap times interval length. A common reciprocal cutoff gives the
    printed strict defect threshold. This supporting pointwise step only
    needs the stated finite derivatives, not an additional regularity
    premise. *)
Lemma excess_arc_derivative_in_defect_locus (R : realType)
    (g : R -> real_line_metric R) (x v w : R) :
  has_real_curve_derivative g x v -> has_real_curve_derivative (arc_length g) x w ->
  `|v|<w -> exists n : nat, real_variation_defect_locus g n x.
Proof.
move=> hG hS hgap.
pose gap := w-`|v|.
have hgap0 : 0<gap by rewrite /gap subr_gt0.
pose gamma := gap/4.
have hgamma : 0<gamma by rewrite /gamma divr_gt0 // ltr0n.
have [ds [hds hSB]] := @real_derivative_interval_bounds R (arc_length g) x w gamma hS hgamma.
have [dg [hdg hGE]] := @real_derivative_interval_error R g x v gamma hG hgamma.
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
have hnorm := ler_normD (g b-g a-v*(b-a)) (v*(b-a)).
rewrite subrK normrM (ger0_norm (ltW hw)) in hnorm.
have hGup := le_trans hnorm (lerD hGerr (lexx _)).
have hdef := lerB hSlo hGup.
have heq : (w-gamma)*(b-a)-(gamma*(b-a)+`|v|*(b-a))=(gap/2)*(b-a).
  by rewrite /gamma /gap; field.
rewrite heq in hdef.
have hstrict : r*(b-a)<(gap/2)*(b-a) by rewrite (ltr_pM2r hw).
have hfinal := lt_le_trans hstrict hdef.
change ((b-a)/(n.+1)%:R<real_variation_defect g a b).
rewrite /real_variation_defect mulrC.
exact hfinal.
Qed.
