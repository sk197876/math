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
  LocallyIntegrableVectorFieldUP LocallyBoundedMeasurableFieldIntegrability SmoothCompactSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ReflexiveLocalDirectionalField.
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


(** Source for [reflexive_local_directional_field_exists]: the original
    D_v f of the locally Lipschitz/reflexive input clause,
    Federer 4.1.2, p. 347, has a measurable locally
    norm-integrable representative preserving every originally defined
    derivative, with zero values only off its actual partial domain. *)
Theorem reflexive_local_directional_field_exists v:
  exists xi:X->Y,
    (forall x w,punctured_norm_limit NY (fun t=>t^-1*:(f (x+t*:v)-f x)) w ->xi x=w) /\
    (forall x,~(exists w,punctured_norm_limit NY (fun t=>t^-1*:(f (x+t*:v)-f x)) w) ->xi x=0) /\
    @is_locally_integrable_vector_field R X Y N NY hN hNY (@euclidean_lebesgue_measure R n) xi /\
    measure_almost_everywhere (@euclidean_lebesgue_measure R n)
      [set x|punctured_norm_limit NY (fun t=>t^-1*:(f (x+t*:v)-f x)) (xi x)].
Proof.
have hF:=metric_local_lipschitz_continuous_whole hLocal.
have hExists:=@reflexive_local_lipschitz_directional_ae R n Y YD YB NY hNY hY hSep
  ed DN hYD eb BN hYB tau hTau hReflexive f hLocal v.
have[xi [hRep [hZero [hMeas hAE]]]]:=@norm_directional_measurable_representative_exists
  R n Y NY hNY f v hF hExists.
have hBound (K:smooth_compact_set hN (fun _=>True)):exists M:R,0<=M /\forall x,smooth_compact_carrier K x ->NY (xi x)<=M.
  have[M [hM [_ hDer]]]:=@norm_compact_lipschitz_directional_bound R n Y NY hNY f v hLocal K.
  exists M; split; first exact hM.
  move=>x hx.
  case:(pselect (exists w,punctured_norm_limit NY (fun t=>t^-1*:(f (x+t*:v)-f x)) w))=>[[w hw]|hn].
  - rewrite (hRep x w hw); exact:(@hDer x hx w hw).
  - by rewrite (hZero x hn) (real_seminorm_zero hNY.1).
have hField:=@locally_bounded_measurable_field_locally_integrable R n Y NY hNY xi hMeas hBound.
exists xi; split; first exact hRep.
split; first exact hZero.
by split.
Qed.
End ReflexiveLocalDirectionalField.
