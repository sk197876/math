(** Federer (1969), 2.4.14, p. 88: the magnitude of a signed-power
    dependence coefficient is determined by the powered integrals. This
    supporting consequence includes a zero coefficient, handled by null
    modification. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialNormPower RealPower SignedRealPower PartialSignedPower MeasureUpperIntegralScale
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralScaleLaw
  MeasureIntegralAlmostEquality MeasureIntegralUniqueness MeasureDensityNullSets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [signed_dependence_power_integral]: supporting relation
    between the powered integrals in the equality case of Federer 2.4.14, p.
    88 The coefficient may have either sign or vanish; the supplied integral
    is finite. *)
Lemma signed_dependence_power_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p q c b : R)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  (0 < p)%R -> (0 < q)%R ->
  measure_almost_everywhere mu (partial_signed_power_dependence_locus p q c f g) ->
  is_measure_integral mu (partial_norm_power (fun x : R => `|x|%R) q g) b%:E ->
  is_measure_integral mu (partial_norm_power (fun x : R => `|x|%R) p f) (`|c|*b)%:E.
Proof.
move=> hp hq he hgi.
have hnum a d : signed_real_power p a = (c * signed_real_power q d)%R ->
    real_power `|a|%R p = (`|c|*real_power `|d|%R q)%R.
  move=> had; have hh := congr1 (fun z : R => `|z|%R) had.
  by rewrite [RHS]normrM !signed_real_power_absolute // in hh.
have [hc|hc] := eqVneq c 0%R.
- rewrite hc normr0 mul0r.
  apply: (@measure_integral_almost_equal R X mu hm _ _ 0 (@measure_extended_zero_integral R X mu hm)).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he).
  move=> x [a [d [ha [hd had]]]]; exists 0; split=> //; exists a; split=> //.
  by rewrite (hnum a d had) hc normr0 mul0r.
- have hcpos : (0 < `|c|)%R by rewrite normr_gt0.
  have hs := @measure_integral_positive_scale R X mu hm `|c|%R _ b%:E hcpos hgi.
  rewrite -EFinM in hs.
  apply: (@measure_integral_almost_equal R X mu hm _ _ (`|c|*b)%:E hs).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he).
  move=> x [a [d [ha [hd had]]]]; exists (real_power `|a|%R p)%:E; split.
  + exists (real_power `|d|%R q)%:E; split; first by exists d; split.
    by rewrite -EFinM -(hnum a d had).
  + exists a; by split.
Qed.

(** Source for [unit_signed_dependence_coefficient_absolute]: supporting
    normalised coefficient calculation in Federer 2.4.14, p. 88 Unit powered
    integrals force the coefficient to have absolute value one. *)
Lemma unit_signed_dependence_coefficient_absolute (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p q c : R)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  (0 < p)%R -> (0 < q)%R ->
  measure_almost_everywhere mu (partial_signed_power_dependence_locus p q c f g) ->
  is_measure_integral mu (partial_norm_power (fun x : R => `|x|%R) p f) 1 ->
  is_measure_integral mu (partial_norm_power (fun x : R => `|x|%R) q g) 1 ->
  (`|c| = 1)%R.
Proof.
move=> hp hq he hfi hgi.
have hi := @signed_dependence_power_integral R X mu hm p q c 1%R f g hp hq he hgi.
rewrite mulr1 in hi.
have hc := @measure_integral_unique R X mu _ `|c|%:E 1 hi hfi.
exact (EFin_inj hc).
Qed.
