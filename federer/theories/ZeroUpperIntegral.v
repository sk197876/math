(** Federer (1969), 2.10.26, p. 190: the reduction for source sets of zero
    measure uses 2.10.25 and the fact that a nonnegative function of upper
    integral zero vanishes almost everywhere. Prove that supporting fact for
    arbitrary measures from characteristic upper bounds 2.4.5, p. 84, and
    upper-integral order/scaling 2.4.3, pp. 81–82. The original function
    need not be measurable. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology ExtendedRealReciprocalBounds
  PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci MeasureUP MeasureBasic MeasureAlmostUP
  MeasureAlmostBasic MeasureAlmostEquality MeasurableFunctionUP MeasurableTotalBasic
  MeasurableAlmostModification CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureStepIntegralIdentification MeasureIntegralUP MeasureIntegralBounds MeasureCharacteristicUpperBound MeasureUpperIntegralMonotone MeasureUpperIntegralScale.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_upper_integral_superlevel_bound]:
    supporting positive-level estimate for the null-set
    reduction in 2.10.26, p. 190. Compare a
    scaled characteristic function with f using 2.4.3(2),(5),
    pp. 81–82, and 2.4.5, p. 84.
    Neither f nor its superlevel set is assumed measurable. *)
Theorem nonnegative_upper_integral_superlevel_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> extended_real_line R) (c : R) :
  (forall x, 0<=f x) -> (0<c)%R ->
  c%:E*mu [set x | c%:E<f x]<=measure_upper_integral mu (partial_function_total f).
Proof.
move=> hf hc.
pose A := [set x | c%:E<f x].
pose s := @CharacteristicFunction.value R X A.
have hs := @CharacteristicFunction.laws R X A.
pose g := partial_real_function_embed (partial_function_total s).
have hchar := @measure_characteristic_upper_bound R X mu hm A s hs.
have hC : 0<=c%:E by rewrite lee_fin; exact: ltW hc.
apply: le_trans (lee_wpmul2l hC hchar) _.
rewrite -(@measure_upper_integral_positive_scale R X mu hm c g hc).
apply: (@measure_upper_integral_monotone R X mu hm).
apply: (@measure_almost_everywhere_mono R X mu hm setT _ _
  (measure_almost_everywhere_true hm))=> x _.
exists (c%:E*(s x)%:E),(f x); split.
- exists (s x)%:E; split=> //; exists (s x); by split.
- split=> //; case: (pselect (A x))=> hx.
  + rewrite /s (characteristic_on_set hs hx) mule1; exact: ltW hx.
  + rewrite /s (characteristic_off_set hs hx) mule0; exact: hf.
Qed.

(** Source for [nonnegative_zero_upper_integral_almost_zero]:
    supporting zero-integral inference used in 2.10.26,
    p. 190. Each positive reciprocal superlevel is
    null, and their countable union contains all
    nonzero values of the nonnegative function. *)
Theorem nonnegative_zero_upper_integral_almost_zero (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> extended_real_line R) :
  (forall x, 0<=f x) -> measure_upper_integral mu (partial_function_total f)=0 ->
  measure_almost_everywhere mu [set x | f x=0].
Proof.
move=> hf hzero.
pose c n := ((n.+1%:R : R)^-1)%R.
pose A n := [set x | (c n)%:E<f x].
have hc n : (0<c n)%R by rewrite /c invr_gt0 ltr0n.
have hnull n : mu (A n)=0.
  have hh := nonnegative_upper_integral_superlevel_bound hm hf (hc n).
  rewrite hzero in hh.
  have hfin : (c n)%:E \is a fin_num by rewrite fin_numE.
  have hpos : 0<(c n)%:E by rewrite lte_fin.
  have he := @lee_pmul2l R (c n)%:E hfin hpos (mu (A n)) 0.
  rewrite mule0 in he; rewrite he in hh.
  apply/eqP; by rewrite eq_le hh (measure_nonnegative hm).
have hn n : measure_almost_everywhere mu (~` A n) by rewrite /measure_almost_everywhere setCK.
have hall := @measure_almost_everywhere_countable R X [the choiceType of (nat : Type)]
  mu hm setT (fun n=>~` A n) (countableP _) (fun n _=>hn n).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hall)=> x hx.
apply/eqP; rewrite eq_le (hf x) andbT.
apply: (@extended_real_reciprocal_upper_bound R (f x) 0%R)=> n.
rewrite add0r leNgt; apply/negP=> hlt; exact: (hx n Logic.I hlt).
Qed.

(** Source for [nonnegative_zero_upper_integral_measurable]:
    supporting measurability inference for the zero-source-mass
    reduction in 2.10.26, p. 190. Completeness of
    the measure makes an almost-everywhere zero total
    function measurable; no measurability premise is added. *)
Theorem nonnegative_zero_upper_integral_measurable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> extended_real_line R) :
  (forall x, 0<=f x) -> measure_upper_integral mu (partial_function_total f)=0 ->
  is_measure_measurable_function mu (partial_function_total f).
Proof.
move=> hf hzero.
have he := nonnegative_zero_upper_integral_almost_zero hm hf hzero.
apply: (@measurable_function_almost_equal R X (extended_real_line R) mu hm
  (partial_function_total (fun _ : X=>(0 : extended_real_line R))) (partial_function_total f)
  (@measurable_total_constant R X (extended_real_line R) mu hm 0)).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he)=> x hx.
exists 0; split=> //; exact hx.
Qed.
