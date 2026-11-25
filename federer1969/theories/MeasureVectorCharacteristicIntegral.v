(** Federer (1969), 2.4.12, pp. 87–88: elementary finite-image functions
    belong to the subspace carrying the vector integral. The characteristic
    function is supplied by its laws and the finite measure by its real
    value. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground PartialFunctionUP PartialFunctionBasic PartialNormPower RealPower
  MeasureUP MeasureBasic CharacteristicFunctionUP CharacteristicVectorPiece MeasurableNormedBasic
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureStepIntegralIdentification MeasureCharacteristicIntegral
  MeasureFiniteRealScaleIntegral MeasureLpNorm MeasureLpMembershipUP MeasureLpCountableMeasurability
  ExtendedPositivePower MeasureVectorIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_vector_characteristic_integral]: direct elementary
    vector integral used in Federer 2.4.12, pp. 87–88 This proves full L1
    membership and the dual specification, including y=0 and phi(A)=0. *)
Theorem measure_vector_characteristic_integral (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (s : X -> real_line_metric R) (b : R) (y : V) :
  is_characteristic_function A s -> measure_measurable mu A -> mu A = b%:E ->
  is_measure_vector_integral mu
    (partial_function_total (fun x => (s x *: y : real_norm_metric_space hN))) (b *: y)%R.
Proof.
move=> hs hA hb.
pose f := partial_function_total (fun x => (s x *: y : real_norm_metric_space hN)).
have hfA := @measurable_normed_characteristic_piece R X V N hN mu hm A s
  (fun _ => (y : real_norm_metric_space hN)) hs hA
  (@measurable_normed_total_constant R X V N hN mu hm y).
have hchar := @measure_characteristic_integral R X mu hm A s hs hA; rewrite hb in hchar.
have hnorm := @measure_finite_real_total_scale_integral R X mu hm s b (N y) hchar.
have hval x : real_power (N (s x *: y)%R) 1%R = (N y*s x)%R.
  rewrite real_power_one_exponent; last exact: real_seminorm_nonnegative hN.1 _.
  have [hx|hx] := pselect (A x).
  - by rewrite (characteristic_on_set hs hx) scale1r mulr1.
  - by rewrite (characteristic_off_set hs hx) scale0r (real_seminorm_zero hN.1) mulr0.
have hni : is_measure_integral mu (partial_norm_power N 1%R f) (N y*b)%:E.
  apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ hnorm)=> x z; split.
  - move=> [r [hr he]]; exists (s x *: y)%R; split=> //; by rewrite hval hr.
  - move=> [v [hv he]]; exists (N y*s x)%R; split=> //.
    by rewrite -(hv : (s x *: y)%R=v) hval in he.
have hb0 : (0 <= b)%R by have h := measure_nonnegative hm A; rewrite hb lee_fin in h.
have hn0 : 0 <= (N y*b)%:E by rewrite lee_fin mulr_ge0 //; exact: real_seminorm_nonnegative hN.1 _.
have hfn : measure_lp_norm mu N 1%R f = (N y*b)%:E.
  rewrite (@measure_lp_norm_of_integral R X V N hN mu 1%R f _ hm (lexx _) hfA.1 hni).
  by rewrite invr1 extended_positive_power_one.
have hfinite : measure_lp_norm mu N 1%R f < +oo by rewrite hfn ltry.
split.
- split; first exact: lexx.
  split=> //; split=> //.
  exact (@finite_lp_norm_countably_measurable R X V N hN mu hm 1%R f (lexx _) hfA.1 hfinite).
- move=> a ha; rewrite linearZ /=.
  change (is_measure_integral mu (partial_functional_evaluation f a) (b*a y)%:E).
  rewrite mulrC.
  have hi := @measure_finite_real_total_scale_integral R X mu hm s b (a y) hchar.
  have heval x : a (s x *: y)%R=(a y*s x)%R.
    rewrite linearZ; change ((s x*a y)%R=(a y*s x)%R); exact: mulrC.
  apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ hi)=> x z; split.
  + move=> [r [hr he]]; exists (s x *: y)%R; split=> //.
    by rewrite heval hr.
  + move=> [v [hv he]]; exists (a y*s x)%R; split=> //.
    by rewrite -(hv : (s x *: y)%R=v) heval in he.
Qed.
