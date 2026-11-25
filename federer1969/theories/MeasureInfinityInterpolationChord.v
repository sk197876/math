(** Federer (1969), 2.4.17, p. 90: logarithmic convexity used at infinity.
    This supporting estimate writes that chord explicitly in the original
    exponent coordinate. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP RealPower
  MeasureUP MeasurableFunctionUP MeasureLpNorm MeasureEssentialNorm
  MeasureReciprocalInterpolationInfinity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_infinity_interpolation_chord]: Supporting Federer
    2.4.17, p. 90.The fixed finite exponent is s and the variable exponent p
    is larger than s. *)
Lemma measure_infinity_interpolation_chord (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (s p A B : R) (f : partial_function X (real_norm_metric_space hN)) :
  (1 <= s)%R -> (s < p)%R -> (0 < A)%R -> is_measure_measurable_function mu f ->
  measure_essential_norm mu N f=A%:E -> measure_lp_norm mu N s f=B%:E ->
  measure_lp_norm mu N p f <= (real_power A (1-s/p)%R * real_power B (s/p)%R)%:E.
Proof.
move=> hs hsp hA hf hea hsb.
have hs0 : (0 < s)%R := lt_le_trans ltr01 hs.
have hp0 : (0 < p)%R := lt_trans hs0 hsp.
have hsne : s != 0%R by rewrite gt_eqF.
have hsi : (0 < s^-1)%R by rewrite invr_gt0.
have hsi1 : (s^-1 <= 1)%R by rewrite invf_le1.
have hb : (0 < s/p)%R by rewrite divr_gt0.
have hb1 : (s/p < 1)%R by rewrite ltr_pdivrMr // mul1r.
have ha : (0 < 1-s/p)%R by rewrite subr_gt0.
have hab : (1-s/p+s/p= 1)%R by rewrite subrK.
have hbe : ((s/p) * s^-1=p^-1)%R by rewrite mulrAC mulfV // div1r.
have hh := @measure_reciprocal_interpolation_infinity R X V N hN mu hm s^-1 (1-s/p)%R (s/p)%R A B f hsi hsi1 ha hb hab hA hf hea.
rewrite invrK in hh; have h := hh hsb.
by rewrite hbe invrK in h.
Qed.
