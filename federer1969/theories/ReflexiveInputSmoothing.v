(** Federer (1969), 4.1.2, p. 347: actual directional
    derivatives exist almost everywhere for Lipschitz inputs into
    a separable reflexive Banach space. The original curve theorem
    2.9.22 and the proved Borel-domain Fubini transfer supply them. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets cardinality reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  NormMetricScaleContinuity NormedCurveDerivativeUP NormDirectionalQuotientContinuity
  ContinuousDualUP ContinuousDualNorm ContinuousBidualUP SeparableReflexiveLipschitzDifferentiation
  EuclideanLebesgueDimensions EuclideanDirectionalNullSlices RealMetricBackground LebesgueScalarMeasure
  MeasureAlmostUP MeasureAlmostBasic TopologicalBorel LipschitzUP
  EuclideanLocalLipschitzRepresentative ReflexiveLipschitzDirectionalAE
  ReflexiveLocalLipschitzDirectionalAE NormDirectionalMeasurableRepresentative
  MetricLocalLipschitzContinuity NormCompactLipschitzDirectionalBound
  LocallyIntegrableVectorFieldUP LocallyBoundedMeasurableFieldIntegrability SmoothCompactSet
  ReflexiveLocalDirectionalField SmoothingKernelUP SmoothingDilationUP SmoothingConvolutionUP SmoothingConvolutionExistence
  FiniteCoordinates NormFirstDirectionalGraph NormIteratedDirectionalSealed NormPartialDerivative
  PartialFunctionUP PartialFunctionBasic MeasureAlmostEquality
  PartialSmoothingConvolutionUP PartialConvolutionExtension SmoothingLocalLipschitzInput.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ReflexiveInputSmoothing.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable Y YD YB:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Hypothesis hSep:is_separable_normed_space hNY.
Variable ed:Hom YD (Hom Y R^o).
Variable DN:YD->R.
Hypothesis hYD:is_continuous_dual hNY ed DN.
Variable eb:Hom YB (Hom YD R^o).
Variable BN:YB->R.
Hypothesis hYB:is_continuous_dual (continuous_dual_norm_is_norm hYD) eb BN.
Variable tau:Hom Y YB.
Hypothesis hTau:is_bidual_embedding ed eb tau.
Hypothesis hReflexive:is_reflexive_embedding tau.
Variable f:X->Y.

Hypothesis hLocal:is_locally_metric_lipschitz setT
  (f:real_norm_metric_space hN->real_norm_metric_space hNY).



Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable e:R.
Hypothesis he:0<e.
Variable g:X->Y.
Hypothesis hConv:is_smoothing_convolution hNY (family e) f g.

(** Source for [reflexive_input_smoothing_commutes]: the complete
    locally Lipschitz/reflexive clause of Federer 4.1.2, p. 347.
    The convolution on the right retains the actual partial
    derivative's full original graph and conull domain.
    Its actual vector integrals are proved to exist. *)
Theorem reflexive_input_smoothing_commutes v:
  exists q:X->Y,
    @is_partial_smoothing_convolution R n Y NY hNY (family e)
      (@NormIteratedDirectional.value R X Y NY hNY (fun _=>True) f [::v]) q /\
    forall a:X,punctured_norm_limit NY (fun t=>t^-1*:(g (a+t*:v)-g a)) (q a).
Proof.
have[xi [hRep [hZero [hField hAE]]]]:=@reflexive_local_directional_field_exists
  R n Y YD YB NY hNY hY hSep ed DN hYD eb BN hYB tau hTau hReflexive f hLocal v.
have[q hQ]:=@smoothing_convolution_exists R n Y NY hNY hY hSep phi hPhi family hFamily e he xi hField.
have hAlmost:measure_almost_equal (@euclidean_lebesgue_measure R n)
    (@NormIteratedDirectional.value R X Y NY hNY (fun _=>True) f [::v])
    (partial_function_total (fun x=>(xi x:real_norm_metric_space hNY))).
  apply:(@measure_almost_everywhere_mono R X (@euclidean_lebesgue_measure R n)
    (euclidean_lebesgue_is_measure R n) _ _ _ hAE).
  move=>x hx; exists (xi x); split; last reflexivity.
  exact:(@norm_first_directional_graph_limit R X Y NY hNY f v x (xi x)).2 hx.
exists q; split.
- exact:(@partial_smoothing_convolution_extension_iff R n Y NY hNY (family e)
    (@NormIteratedDirectional.value R X Y NY hNY (fun _=>True) f [::v]) xi q hAlmost).2 hQ.
- move=>a; exact:(@smoothing_local_lipschitz_input_derivative R n Y NY hNY hY hSep
    phi hPhi family hFamily e he f xi g q hLocal v hRep hZero hAE hConv hQ a).
Qed.

(** Source for [reflexive_input_smoothing_coordinate]: the exact
    original coordinate form D_j(Phi_epsilon*f)=Phi_epsilon*D_j f,
    Federer 4.1.2, p. 347. This uses the existing
    coordinate partial derivative predicate of 3.1.1. *)
Theorem reflexive_input_smoothing_coordinate (i:'I_n):
  exists q:X->Y,
    @is_partial_smoothing_convolution R n Y NY hNY (family e)
      (@NormIteratedDirectional.value R X Y NY hNY (fun _=>True) f [::(@coordinate_basis R n i)]) q /\
    forall a:X,has_norm_partial_derivative NY g a i (q a).
Proof.
exact:(reflexive_input_smoothing_commutes (@coordinate_basis R n i)).
Qed.
End ReflexiveInputSmoothing.
