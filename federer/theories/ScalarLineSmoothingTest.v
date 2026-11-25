(** Federer (1969), 4.1.3, p. 348: one common scalar
    test supplies the separated normalized kernel. Transport
    the existing one-dimensional Euclidean regularising kernel
    through the original isometric scalar-line identification. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  NormRegularity NormRegularityOperations NormRegularityLinearMaps NormClassZeroTopology
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  InnerMetric EuclideanOneCoordinate EuclideanOneNormDifferential EuclideanScalarCoordinateMaps
  SmoothCompactSet SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation SmoothTestRepresentation
  CompactSupportFunctionUP SmoothingKernelUP SmoothingDilationUP SmoothingDilationSupport SmoothingDilationSmooth
  SmoothingDilationNonzeroRadius SmoothingDilationIntegral EuclideanLebesgueDimensions
  ScalarEuclideanApproximateLimits RealMetricBackground MeasurePushforward InjectivePushforwardIntegral
  MeasureIntegralUP MeasureIntegralGraphEquivalence SummableRealFunctionUP LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ScalarLineSmoothingTest.
Variable R:realType.
Local Notation X := (R_n R 1).
Local Notation N := (inner_norm (@euclidean_inner_productP R 1)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R 1)).
Local Notation hR := (@scalar_absolute_value_norm R).
Variable A:lmodType R.
Variable av:A->R^o->R^o.
Hypothesis hA:is_smooth_function_space hR hR (fun _=>True) av.
Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable r:R.
Hypothesis hr:0<r.

(** Source for [scalar_line_smoothing_test_exists]: an actual
    scalar test with positive support bound r, nonnegative
    values and original integral one, supporting the common
    factor gamma in Federer 4.1.3, p. 348. *)
Theorem scalar_line_smoothing_test_exists:
  exists gamma:smooth_test_space hA,
    (forall t:R,smooth_test_value hA gamma t=family r (euclidean_one_embed t)) /\
    (forall t:R,0<=smooth_test_value hA gamma t) /\
    (forall t:R,smooth_test_value hA gamma t<>0 ->`|t|<=r) /\
    is_measure_integral (@lebesgue_scalar_measure R)
      (real_total_integrand (smooth_test_value hA gamma)) (1:R)%:E.
Proof.
pose psi:=fun t:R^o=>(family r (euclidean_one_embed t):R^o).
have hEmbed:linear (fun t:R^o=>(euclidean_one_embed t:X)).
  move=>c t s; apply/ffunP=>i; by rewrite /euclidean_one_embed !ffunE.
pose M:Hom R^o X:=@HomMap R R^o X (fun t:R^o=>(euclidean_one_embed t:X))
  (introT (asboolP _) hEmbed).
have hM:norm_bounded_linear (fun t:R^o=>`|t|) N M.
  exists 1; split; first exact:ler01.
  move=>t; change (N (euclidean_one_embed t)<=1*`|t|).
  by rewrite euclidean_one_norm_coordinate /euclidean_one_embed ffunE mul1r.
have hSmooth:norm_class_all_orders hR hR (fun _=>True) psi.
  move=>k; exact:(@norm_class_precompose_linear R R^o X R^o _ N _ hR hN hR
    (fun _=>True) (family r) M k hM
    (@smoothing_dilation_smooth R 1 phi hPhi family hFamily r hr k)).
pose C:=@real_function_support R (real_norm_metric_space hN) (family r).
have hC:compact C:=@smoothing_dilation_support_compact R 1 phi hPhi family hFamily r hr.
have hPC:continuous (fun x:real_norm_metric_space hN=>(euclidean_one_project x:real_norm_metric_space hR)).
  have hc:=@norm_class_linear R X R^o N _ hN hR (fun _=>True)
    (euclidean_scalar_coordinate_map ord0) 0%N
    (fun x _=>norm_full_domain_interior N x) (euclidean_scalar_coordinate_bounded ord0).
  move=>x; exact:(@norm_class_zero_continuous_at R X R^o N _ hN hR
    (fun _=>True) _ x (norm_class_continuous hc) I).
pose K0: set R^o:=(fun x:real_norm_metric_space hN=>(euclidean_one_project x:real_norm_metric_space hR)) @` C.
have hK0:compact [set t:real_norm_metric_space hR|K0 t].
  exact:(continuous_compact (continuous_subspaceT hPC) hC).
pose K:=@Build_smooth_compact_set R R^o _ hR (fun _=>True) K0 (fun _ _=>I) hK0.
have hOff t:~smooth_compact_carrier K t ->psi t=0.
  move=>ht; apply:(@real_function_zero_off_support R (real_norm_metric_space hN) (family r)
    (euclidean_one_embed t)).
  move=>hIn; apply:ht; exists (euclidean_one_embed t)=>//.
  exact:euclidean_one_embedK.
have[gamma hGamma]:=@smooth_test_represents_compact_function R R^o R^o _ _ hR hR
  (fun _=>True) A av hA K psi hSmooth hOff.
have hValue t:smooth_test_value hA gamma t=family r (euclidean_one_embed t):=hGamma t I.
exists gamma; split; first exact hValue.
split.
- move=>t; rewrite hValue; exact:(@smoothing_dilation_nonnegative R 1 phi hPhi family hFamily r hr).
split.
- move=>t hn; rewrite leNgt; apply/negP=>hLarge.
  have hNorm:N (euclidean_one_embed t)=`|t| by rewrite euclidean_one_norm_coordinate /euclidean_one_embed ffunE.
  have hZero:=@smoothing_dilation_zero_beyond_radius R 1 phi family hPhi hFamily r hr
    (euclidean_one_embed t).
  rewrite hNorm in hZero.
  apply:hn; by rewrite hValue hZero.
- pose mu:=@euclidean_lebesgue_measure R 1.
  have hPush:measure_pushforward (@euclidean_one_project R) mu=@lebesgue_scalar_measure R.
    apply:funext=>B; exact:Logic.eq_sym (euclidean_one_project_measure_preimage B).
  have hIff:=@injective_pushforward_integral_iff R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R 1)] R mu (euclidean_lebesgue_is_measure R 1)
    (@euclidean_one_project R) (real_total_integrand (smooth_test_value hA gamma))
    (can_inj (@euclidean_one_projectK R)) (1:R)%:E.
  rewrite hPush in hIff; apply:hIff.1.
  have hIntegral:=@smoothing_dilation_integral_one R 1 phi family hPhi hFamily r hr.
  apply:(measure_integral_graph_equivalent _ hIntegral)=>x z.
  rewrite !real_total_integrand_graph hValue euclidean_one_projectK.
  reflexivity.
Qed.
End ScalarLineSmoothingTest.
