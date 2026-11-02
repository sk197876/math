(** Federer (1969), 2.4.14, p. 88: sufficiency of one oriented signed-power
    dependence relation after normalisation. Unit powered integrals force
    the dependence coefficient to be one or minus one. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower PartialScalarProduct PartialSignedPower
  MeasureSignedPowerCoefficient MeasureHolderUnitConverse MeasureUP MeasureAlmostUP MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_holder_unit_dependence_integral]: the normalised
    sufficiency inference in Federer 2.4.14, p. 88 An arbitrary real
    dependence coefficient is reduced to the two possible signs using the
    unit powered integrals. *)
Lemma measure_holder_unit_dependence_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p q k : R)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  (0 < p)%R -> (0 < q)%R -> (p^-1 + q^-1 = 1)%R ->
  is_measure_integral mu (partial_norm_power (fun x : R => `|x|%R) p f) 1 ->
  is_measure_integral mu (partial_norm_power (fun x : R => `|x|%R) q g) 1 ->
  measure_almost_everywhere mu (partial_signed_power_dependence_locus p q k f g) ->
  exists d : R, (`|d| = 1)%R /\ is_measure_integral mu (partial_scalar_product f g) d%:E.
Proof.
move=> hp hq hpq hfi hgi he.
have hk := @unit_signed_dependence_coefficient_absolute R X mu hm p q k f g hp hq he hfi hgi.
have [hk0|hk0] := leP 0%R k.
- rewrite (ger0_norm hk0) in hk; rewrite hk in he.
  exists 1%R; split; first exact: normr1.
  exact (@measure_holder_unit_equal_signed_integral R X mu hm p q f g hp hq hpq hfi hgi he).
- rewrite (ler0_norm (ltW hk0)) in hk.
  have hk' : k=(-1)%R by rewrite -(opprK k) hk.
  rewrite hk' in he.
  exists (-1)%R; split; first exact: normrN1.
  exact (@measure_holder_unit_opposite_signed_integral R X mu hm p q f g hp hq hpq hfi hgi he).
Qed.
