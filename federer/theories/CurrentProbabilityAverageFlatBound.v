(** Federer (1969), 4.1.18, p. 375: average
    the preceding flat estimate using the original
    compact-test dual supremum. All integrals here
    are scalar actions; no topology or Banach
    integral on a space of currents is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentPointEvaluation SmoothCompactSet CurrentFlatNorm
  CurrentFlatDualSeminormUP CurrentFlatDualSeminormSealed CurrentFlatDualSeminormBasic
  ExtendedSupremumUP MeasureUP MeasureIntegralUP MeasureIntegralComparison
  SummableRealFunctionUP SummableRealArithmetic RealTotalCharacteristicBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentProbabilityAverageFlatBound.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation DT:=(@current_test_space R h2 n U hU m).
Local Notation action:=(@current_value R h2 n U hU m).
Variable K:smooth_compact_set
  (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Variable P:choiceType.
Variable mu:set P->\bar R.
Hypothesis hm:is_measure mu.
Variable w:P->R.
Hypothesis hPositive:forall z,0<=w z.
Hypothesis hUnit:is_measure_integral mu (real_total_integrand w) 1%:E.
Variable S:P->C.
Variables Q T:C.
Hypothesis hQ:forall omega:DT,is_measure_integral mu
  (real_total_integrand (fun z=>w z*action (S z) omega)) (action Q omega)%:E.
Variable c:R.
Hypothesis hBound:forall z,w z<>0 ->
  (@current_flat_norm R h2 n m U hU K (S z-T)<=c%:E)%E.

(** Source for [current_probability_average_flat_bound]:
    the original flat dual test bound survives
    the probability average, by 2.4.4(5) and
    4.1.12, supporting the literal smoothing flat
    error in Federer 4.1.18, p. 375. *)
Theorem current_probability_average_flat_bound:
  (@current_flat_norm R h2 n m U hU K (Q-T)<=c%:E)%E.
Proof.
have hSubtract (A B:C) (omega:DT):
    action (A-B) omega=action A omega-action B omega.
  change (@current_point_evaluation R h2 n m U hU omega (A-B)=
    @current_point_evaluation R h2 n m U hU omega A-
    @current_point_evaluation R h2 n m U hU omega B).
  exact:linearB.
apply:(extended_supremum_least (@CurrentFlatDualSeminorm.laws R h2 n m U hU K
  (action (Q-T))))=>a [omega [hOmega <-]].
have hConstant:=@real_total_integral_scale R P mu hm w 1
  (action T omega) hUnit.
rewrite mulr1 in hConstant.
have hDifference:=@real_total_integral_subtract R P mu hm
  (fun z=>w z*action (S z) omega) (fun z=>action T omega*w z)
  (action Q omega) (action T omega) (hQ omega) hConstant.
have hFunction:(fun z=>w z*action (S z) omega-action T omega*w z)=
    (fun z=>w z*action (S z-T) omega).
  apply:funext=>z;rewrite hSubtract;ring.
rewrite hFunction -hSubtract in hDifference.
have hUpper:=@real_total_integral_scale R P mu hm w 1 c hUnit.
rewrite mulr1 in hUpper.
apply:(@measure_integral_monotone R P mu hm _ _ _ _ hDifference hUpper).
apply:(@real_total_pointwise_order_almost R P mu hm)=>z.
case:(pselect (w z=0))=>[->|hz];first by rewrite mul0r mulr0.
have hTest:=@current_flat_dual_unit_upper R h2 n m U hU K
  (action (S z-T)) omega hOmega.
have hValue:action (S z-T) omega<=c.
  have h:=le_trans hTest (@hBound z hz).
  by rewrite lee_fin in h.
rewrite [c*w z]mulrC.
exact:(@ler_wpM2l R (w z) (@hPositive z) (action (S z-T) omega) c hValue).
Qed.
End CurrentProbabilityAverageFlatBound.
