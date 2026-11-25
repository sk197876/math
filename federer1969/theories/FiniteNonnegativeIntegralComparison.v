(** Federer (1969), 3.2.31, p. 269: supporting finite summation
    of local fibre-integral bounds. This is finite nonnegative
    integration from 2.4.8, p. 84, followed by monotonicity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals
  constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  MeasureIntegralBounds MeasureIntegralUniqueness MeasureUpperIntegralMonotone MeasureUpperIntegralNonnegative
  NonnegativeSum FiniteCoverMeasureBounds TotalCountableNonnegativeIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_nonnegative_integral_comparison]: supporting
    finite summation in Federer 3.2.31, p. 269. An arbitrary
    nonnegative integrand bounded by a finite sum has upper
    integral at most the sum of the actual component integrals.
    The index type may be empty and values may be infinite;
    no measurability of the smaller integrand is required. *)
Theorem finite_nonnegative_integral_comparison (R:realType) (X:choiceType) (I:finType)
    (mu:set X->\bar R) (hm:is_measure mu) (f:X->extended_real_line R)
    (u:I->X->extended_real_line R) (a:I->\bar R):
  (forall i x,0<=u i x) ->
  (forall i,is_measure_integral mu (partial_function_total (u i)) (a i)) ->
  (forall x,f x<=\sum_i u i x) ->
  measure_upper_integral mu (partial_function_total f)<=\sum_i a i.
Proof.
move=>hu hi hBound.
have hNonnegative i:0<=a i.
  have he:=measure_upper_integral_unique (measure_upper_integral_specification mu _) (hi i).2.1.
  rewrite -he.
  apply:(measure_upper_integral_nonnegative hm).
  apply:(measure_almost_everywhere_mono hm _ (measure_almost_everywhere_true hm))=>x _.
  exists (u i x); by split.
have hSum:=@total_countable_nonnegative_integral R X I mu hm setT u a
  (countableP _) (fun i _=>hu i) (fun i _=>hi i).
have hFun:(fun x=>nonnegative_sum setT (fun i=>u i x))=(fun x=>\sum_i u i x).
  apply:funext=>x; exact:finite_type_nonnegative_sum (fun i=>hu i x).
have hValues:nonnegative_sum setT a=\sum_i a i.
  exact:finite_type_nonnegative_sum hNonnegative.
rewrite hFun hValues in hSum.
have hVal:=measure_upper_integral_unique (measure_upper_integral_specification mu _) hSum.2.1.
rewrite -hVal; apply:(measure_upper_integral_monotone hm).
apply:(measure_almost_everywhere_mono hm _ (measure_almost_everywhere_true hm))=>x _.
exists (f x),(\sum_i u i x); split=>//; by split=>//; exact:hBound.
Qed.
