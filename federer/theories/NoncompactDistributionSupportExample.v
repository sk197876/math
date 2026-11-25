(** Federer (1969), 4.1.1, p. 345: the
    scalar Lebesgue integration distribution on R^1 has
    noncompact support. This concrete original instance
    uses the actual sealed smooth-function space, its
    final test topology and its continuous real dual. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormOpenDomainLaws GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness EuclideanLebesgueDimensions MeasureUP MeasureIntegralUP SummableRealFunctionUP
  SmoothFunctionSpaceUP SmoothFunctionSpaceSealed SmoothFunctionDerivativesSealed SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology
  ContinuousRealDual FunctionalSupportUP ScalarIntegralDistribution ScalarIntegralDistributionSupport
  EuclideanDistributionMeasureContext NormCompactOpenDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section NoncompactDistributionSupport.
Variable R:realType.
Local Notation X := (R_n R 1).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 1)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R 1)).
Local Notation hR := (@scalar_absolute_value_norm R).
Local Notation hFull := (fun x:X=>fun _:True=>norm_full_domain_interior NX x).
Local Notation E := (@SmoothFunctionSpace.space R X R^o NX (fun t:R^o=>`|t|) hNX hR setT hFull).
Local Notation ev := (@SmoothFunctionSpace.value R X R^o NX (fun t:R^o=>`|t|) hNX hR setT hFull).
Local Notation hE := (@SmoothFunctionSpace.laws R X R^o NX (fun t:R^o=>`|t|) hNX hR setT hFull).
Local Notation D := (@SmoothFunctionDerivatives.operators R X R^o NX (fun t:R^o=>`|t|) hNX hR setT E ev hE).
Local Notation hD := (@SmoothFunctionDerivatives.laws R X R^o NX (fun t:R^o=>`|t|) hNX hR setT E ev hE).
Local Notation DT := (smooth_test_space hE).
Local Notation value := (smooth_test_value hE).
Local Notation SO := (smooth_test_opens hE hD).
Local Notation hSO := (smooth_test_final_topology_laws hE hD).1.
Local Notation DD := (@continuous_real_dual_space R DT SO hSO).
Local Notation eD := (@continuous_real_dual_evaluation R DT SO hSO).
Local Notation mu := (@euclidean_lebesgue_measure R 1).

(** Source for [noncompact_distribution_support_example]: an
    actual continuous distribution with noncompact support,
    proving the assertion in Federer 4.1.1, p. 345.
    No unproved existence or measure premise remains. *)
Theorem noncompact_distribution_support_example:
  exists T:DD,(forall f:DT,is_measure_integral mu (real_total_integrand (value f)) (eD T f)%:E) /\
    ~@compact (real_norm_metric_space hNX)
      (@smooth_functional_support R X R^o NX hNX setT DT value (eD T)).
Proof.
have [T hT]:=@scalar_integral_distribution_exists R X NX hNX mu (euclidean_lebesgue_is_measure R 1)
  (@euclidean_distribution_measure_open R 1) (@euclidean_distribution_measure_compact_finite R 1)
  E ev hE D hD.
exists T; split; first exact hT.
have hSupport:=@scalar_integral_distribution_full_support R X NX hNX 1
  (@coordinate_basis R 1) (@coordinate_basisP R 1) mu (euclidean_lebesgue_is_measure R 1)
  (@euclidean_distribution_measure_open_positive R 1) E ev hE (eD T) hT.
rewrite hSupport.
apply:(@real_norm_nonzero_noncompact R X NX hNX).
exists [ffun _: 'I_1=>(1:R)]=>hZero.
have h:=congr1 (fun y:X=>y ord0) hZero.
have hBad:(1:R)=0 by move:h; rewrite !ffunE.
by move:(oner_neq0 R); rewrite hBad eqxx.
Qed.
End NoncompactDistributionSupport.
