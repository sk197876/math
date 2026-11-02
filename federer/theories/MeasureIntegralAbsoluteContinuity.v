(** Federer (1969), 2.4.11, statement p. 85 and proof p. 86: small
    measurable sets have small absolute integrals for every summable
    function. We retain Federer's strict inequality. Source context:
    PartialUpperTruncation.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialAbsolutePartsGraph PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasureIntegralUP MeasureIntegralAbsolute MeasureSubsetIntegral
  MeasureTruncationSmallTail MeasureTruncationSubsetBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_integral_absolute_continuity]: complete Federer
    2.4.11, pp. 85–86. Given epsilon>0 and a summable partial function,
    there is delta>0 such that every measurable A of measure at most delta
    has integral_A |f| strictly less than epsilon. The proof chooses a
    positive truncation ceiling c and delta=epsilon/(2c). No finite
    ambient-measure hypothesis is introduced. *)
Theorem measure_integral_absolute_continuity (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) (epsilon : R) :
  is_measure_summable mu f -> (0 < epsilon)%R ->
  exists delta : R, (0 < delta)%R /\ forall A : set X,
    measure_measurable mu A -> mu A <= delta%:E ->
    exists a : R, is_measure_subset_integral mu A
      (partial_extended_function_absolute_value f) a%:E /\ (a < epsilon)%R.
Proof.
move=> hf he; have [b hb] := @measure_summable_absolute_value R X mu hm f hf.
pose g := partial_extended_function_absolute_value f.
have hp : measure_almost_everywhere mu (partial_extended_nonnegative_locus g).
  have [z hz] := hf.
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ (measurable_function_domain hz.1)).
  move=> x [y hy]; exists `|y|; split; first by exists y; split.
  exact: abse_ge0.
have he2 : (0 < epsilon/2)%R by rewrite divr_gt0 // ltr0n.
have [n [t [/andP[ht ht2] htail]]] :=
  @measure_summable_truncation_small_tail R X mu hm g b (epsilon/2)%R hb hp he2.
pose c : R := n.+1%:R.
have hc : (0 < c)%R by rewrite /c ltr0n.
have hc0 : c != 0%R by rewrite (gt_eqF hc).
have h20 : (2%R : R) != 0%R by rewrite pnatr_eq0.
pose delta : R := (epsilon/(2*c))%R.
have hd : (0 < delta)%R by rewrite /delta divr_gt0 // mulr_gt0 // ltr0n.
have hcd : (c*delta=epsilon/2)%R.
  by rewrite /delta invfM !mulrA [(c*epsilon)%R]mulrC [(epsilon*c*2^-1)%R]mulrAC mulfK.
exists delta; split=> // A hA hAd.
have [a [ha hab]] := @measure_truncation_subset_bound R X mu hm g A b t c hb hp hA hc ht htail.
exists a; split=> //.
have hcE : (0 : \bar R) < c%:E by rewrite lte_fin.
have hmul : c%:E*mu A <= c%:E*delta%:E.
  exact (@lee_wpmul2l R c%:E (ltW hcE) (mu A) delta%:E hAd).
have hab' : a%:E <= t%:E+c%:E*delta%:E := le_trans hab (leeD2l _ hmul).
rewrite -EFinM -EFinD lee_fin hcd in hab'.
have hehalf : (epsilon/2+epsilon/2=epsilon)%R.
  by rewrite -mulr2n -[LHS]mulr_natr divfK.
have htfinal : (t+epsilon/2 < epsilon)%R.
  have hh : (t+epsilon/2 < epsilon/2+epsilon/2)%R by rewrite ltrD2r.
  by rewrite hehalf in hh.
exact: le_lt_trans hab' htfinal.
Qed.
