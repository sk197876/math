(** Federer (1969), 4.1.4, p. 349: the fixed test
    Phi_delta(x-a)y has vector integral y. The proof reuses
    the original unit kernel integral and the released exact
    invariant vector-integral substitution. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP NormRegularity
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation TranslatedKernelTestUP
  PartialFunctionBasic MeasureIntegralUP SummableRealFunctionUP MeasureVectorIntegralUP
  ContinuousKernelConstantIntegral NormedInvariantVectorIntegral
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section TranslatedKernelUnitMass.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY (fun _=>True) ev.
Variable psi:X->R.
Hypothesis hPsi:norm_class_all_orders hN (@scalar_absolute_value_norm R) (fun _=>True) psi.
Variable r:R.
Hypothesis hOff:forall x,r<N x ->psi x=0.
Hypothesis hUnit:is_measure_integral (@euclidean_lebesgue_measure R n) (real_total_integrand psi) (1:R)%:E.
Variable B:X->Hom Y (smooth_test_space hE).
Hypothesis hB:@is_translated_kernel_tests R X Y N NY hN hNY E ev hE psi B.

(** Source for [translated_kernel_test_unit_integral]: the fixed
    test used in the second displayed limit of Federer 4.1.4,
    p. 349, has its actual vector integral y. *)
Theorem translated_kernel_test_unit_integral a y:
  is_measure_vector_integral (@euclidean_lebesgue_measure R n)
    (partial_function_total (fun x=>(smooth_test_value hE (B a y) x:real_norm_metric_space hNY))) y.
Proof.
have hBase:=@continuous_kernel_constant_integral R n Y NY hNY hY psi r 1 y hPsi hOff hUnit.
rewrite scale1r in hBase.
have hInj:injective (fun x:X=>x-a).
  move=>x z he; have h:=congr1 (fun t:X=>t+a) he; by rewrite !subrK in h.
have hIntegral:=@normed_invariant_total_vector_integral R X Y NY hNY
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
  (fun x:X=>x-a) (fun x=>psi x*:y) y hInj
  (@euclidean_distribution_measure_translation R n (-a)) hBase.
have hEq:(fun x:X=>(psi (x-a)*:y:real_norm_metric_space hNY))=
    (fun x=>(smooth_test_value hE (B a y) x:real_norm_metric_space hNY)).
  apply:funext=>x; by rewrite hB.
by rewrite hEq in hIntegral.
Qed.
End TranslatedKernelUnitMass.
