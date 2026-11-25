(** Constant probability norms supporting Federer (1969), 2.10.35, p. 197:
    in equal dimensions the projected-volume input is constant and
    beta_t(n,n)= 1. Derive constant extended-input norms from the formulas
    of 2.4.12, p. 86, including infinite input and exponent. This is
    supporting integration infrastructure, not an additional printed claim. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedPositivePower RealPower PartialFunctionBasic
  MeasureUP MeasureBasic MeasureAlmostUP MeasurableTotalBasic ProbabilityConstantIntegral
  NonnegativeExtendedExponentNormUP NonnegativeExtendedExponentNorm NonnegativeExtendedNormScale
  NonnegativeExtendedNormFiniteValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [probability_extended_norm_one]: supporting
    constant-one norm used to evaluate
    beta_t(n,n) in 2.10.35, p. 197,
    directly from 2.4.12, p. 86. *)
Lemma probability_extended_norm_one (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (t : \bar R) :
  mu setT= 1%E -> (1<=t)%E ->
  nonnegative_extended_exponent_norm mu (fun _ : X=>1%E) t= 1%E.
Proof.
move=> hprob ht.
have hf := @measurable_total_constant R X (extended_real_line R) mu hm 1%E.
have hn := @nonnegative_extended_exponent_norm_specification R X mu (fun _ : X=>1%E) t
  hm (fun _=>lee_tofin (@ler01 R)) ht hf.
apply: (nonnegative_extended_exponent_norm_unique hn).
clear hn.
case: t ht=> [p| |] ht //=.
- split; first by move: ht; rewrite lee_fin.
  exists 1%E; split.
  + have he : (fun _ : X=>extended_positive_power (1 : \bar R) p)=(fun _ : X=>1%E).
      by apply: funext=> x; rewrite /extended_positive_power /= real_power_one_base.
    rewrite he; exact: (@probability_constant_integral R X mu hm 1 hprob).
  + by rewrite /extended_positive_power /= real_power_one_base.
- split.
  + move=> r [hr hz]; rewrite leNgt; apply/negP=> hbad.
    have he : [set x : X | (r<1)%E]=setT.
      by apply/seteqP; split=> x hx.
    have h10 : (1 : \bar R)%E!= 0%E by rewrite eqe oner_eq0.
    by move: h10; rewrite -hprob -he hz eqxx.
  + move=> b hb; apply: hb; split; first by rewrite lee_fin ler01.
    have he : [set x : X | (1<1 :> \bar R)%E]=set0.
      by apply/seteqP; split=> x; rewrite ltxx.
    by rewrite he (measure_empty hm).
Qed.

(** Source for [probability_nonnegative_extended_constant_norm]: supporting
    constant projected-volume norm in 2.10.35,
    p. 197. The value may be
    infinite; a finite norm would force
    that constant input to be finite almost
    everywhere, contradicting probability mass one. *)
Theorem probability_nonnegative_extended_constant_norm (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (c t : \bar R) :
  mu setT= 1%E -> (0<=c)%E -> (1<=t)%E ->
  nonnegative_extended_exponent_norm mu (fun _ : X=>c) t=c.
Proof.
move=> hprob hc ht; case: c hc=> [a| |] hc.
- have ha : 0<=a by move: hc; rewrite lee_fin.
  have hf := @measurable_total_constant R X (extended_real_line R) mu hm 1%E.
  have hs := @nonnegative_extended_norm_scale R X mu hm (fun _ : X=>1%E) t a
    (fun _=>lee_tofin (@ler01 R)) ht ha hf.
  have he : (fun _ : X=>(a%:E*1)%E)=(fun _ : X=>a%:E).
    by apply: funext=> x; rewrite mule1.
  by rewrite he (probability_extended_norm_one hm hprob ht) mule1 in hs.
- have hf := @measurable_total_constant R X (extended_real_line R) mu hm +oo%E.
  have hn := @nonnegative_extended_exponent_norm_specification R X mu (fun _ : X=>+oo%E) t
    hm (fun _=>leey 0) ht hf.
  apply/eqP; rewrite eq_le leey /= leNgt; apply/negP=> hfin.
  have hae := @finite_nonnegative_extended_norm_almost_finite R X mu hm
    (fun _ : X=>+oo%E) t _ (fun _=>leey 0) hn hfin.
  have he : [set x : X | (+oo : \bar R)%E \is a fin_num]=set0.
    by apply/seteqP; split=> x; rewrite fin_numE eqxx andbF.
  rewrite /measure_almost_everywhere he setC0 hprob in hae.
  have h10 : (1 : \bar R)%E!= 0%E by rewrite eqe oner_eq0.
  by move: h10; rewrite hae eqxx.
- by rewrite leeNy_eq in hc.
Qed.
