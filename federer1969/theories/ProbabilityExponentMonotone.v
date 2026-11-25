(** Federer (1969), 2.4.17, p. 90, final assertion: phi_s(f)<=phi_t(f) when
    phi(X)=1 and 1<=s<t<=infinity. This theorem is Federer's probability
    specialisation, extended harmlessly to s=t. Infinite norm values and the
    infinity exponent are included. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP MeasureUP MeasurableFunctionUP
  MeasureLpNorm MeasureEssentialNorm MeasureExponentDomain
  ProbabilityFiniteLpMonotone ProbabilityInfinityLpMonotone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [probability_measure_exponent_norm_monotone]: the final
    assertion of Federer 2.4.17, p. 90 Arbitrary measurable partial domains
    are retained. *)
Theorem probability_measure_exponent_norm_monotone (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) (s t : \bar R) :
  mu setT= 1 -> 1 <= s -> s <= t -> is_measure_measurable_function mu f ->
  measure_exponent_norm mu f s <= measure_exponent_norm mu f t.
Proof.
move=> hprob hs hst hf.
have [he|hne] := eqVneq s t; first by rewrite he.
case: s hs hst hne=> [s| |] hs hst hne; last by move: hs; rewrite leNgt ltNyr.
- case: t hst hne=> [t| |] hst hne; last by move: hst; rewrite leNgt ltNyr.
  + have hstr : (s < t)%R.
      rewrite lt_neqAle; apply/andP; split=> //; apply/eqP=> he; apply: (negP hne); by rewrite he.
    have ht : (1 <= t)%R := le_trans hs hst.
    have hn := @measure_lp_norm_nonnegative R X R^o _ (scalar_absolute_value_norm R) mu t f hm ht hf.
    have [hfin|hfin] := ltP (measure_lp_norm mu (fun y : R => `|y|%R) t f) +oo; last first.
      exact: le_trans (leey _) hfin.
    have hnum : measure_lp_norm mu (fun y : R => `|y|%R) t f \is a fin_num by rewrite (ge0_fin_numE hn).
    pose a := fine (measure_lp_norm mu (fun y : R => `|y|%R) t f).
    have he : measure_lp_norm mu (fun y : R => `|y|%R) t f=a%:E by rewrite /a fineK.
    change (measure_lp_norm mu (fun y : R => `|y|%R) s f <= measure_lp_norm mu (fun y : R => `|y|%R) t f).
    rewrite he; exact: (@probability_finite_lp_monotone_bound R X R^o _ (scalar_absolute_value_norm R) mu hm s t a f hprob hs hstr hf he).
  + have hn := measure_essential_norm_nonnegative mu (fun y : R => `|y|%R) f.
    have [hfin|hfin] := ltP (measure_essential_norm mu (fun y : R => `|y|%R) f) +oo; last first.
      exact: le_trans (leey _) hfin.
    have hnum : measure_essential_norm mu (fun y : R => `|y|%R) f \is a fin_num by rewrite (ge0_fin_numE hn).
    pose a := fine (measure_essential_norm mu (fun y : R => `|y|%R) f).
    have he : measure_essential_norm mu (fun y : R => `|y|%R) f=a%:E by rewrite /a fineK.
    change (measure_lp_norm mu (fun y : R => `|y|%R) s f <= measure_essential_norm mu (fun y : R => `|y|%R) f).
    rewrite he; exact: (@probability_infinity_lp_monotone_bound R X R^o _ (scalar_absolute_value_norm R) mu hm s a f hprob hs hf he).
- have he : t=+oo by apply/eqP; rewrite eq_le leey hst.
  by move: hne; rewrite he eqxx.
Qed.
