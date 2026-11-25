(** Federer (1969), 4.1.18, p. 375: construct
    the original averaged variation from the earlier
    Radon product and change-of-density laws. The
    compact translation parameter, not a finite spatial
    mass, gives the support properness of addition.
    This file supplies an existence proof only. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import IsotropyGroupTopology Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  NormClassOneUP NormFiniteLinearBound NormBoundedLinearTopology NormScalarClassZeroTopology
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanBlockLinearMaps EuclideanCartesianMap CurrentDomain CurrentCartesianDomain
  CurrentCartesianMeasureSealed CurrentCartesianMeasureRadon EuclideanFullDomainMeasure
  SmoothDomainCompactOpenCover MetricSubsetBackground FiniteNormEquivalence
  EuclideanCompactParameterAddition MeasureUP MeasureBasic MeasurePushforward
  MeasureDensity MeasureDensityUP MeasureIntegralUP RealFiniteDensityIntegral ContinuousRadonDensity
  RadonMeasureUP RadonCarriedProperPushforward RadonCompactScalarIntegral
  RadonWeightedPushforwardIntegral SummableRealFunctionUP FunctionLatticeUP CompactSupportFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section EuclideanKernelProductDensity.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R (n+n)%N).
Local Notation N k:=(inner_norm (@euclidean_inner_productP R k)).
Local Notation hN k:=(inner_norm_real_norm (@euclidean_inner_productP R k)).
Local Notation XT:=(real_norm_metric_space (hN n)).
Local Notation YT:=(real_norm_metric_space (hN (n+n)%N)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior (N n) x).
Local Notation AB:=(@euclidean_cartesian_set R n n Full Full).
Local Notation hAB:=(@current_cartesian_domain_open R n n Full Full hFull hFull).
Local Notation FT:=(current_domain R n Full).
Local Notation CT:=[the metricType R of
  (metric_subset (AB:set YT))].
Local Notation p:=(@euclidean_first_block_map R n n).
Local Notation alpha:=(@euclidean_full_domain_measure R n).
Local Notation hAlpha:=(@euclidean_full_domain_measure_laws R n).1.
Local Notation hAlphaRadon:=(@euclidean_full_domain_measure_laws R n).2.
Variable beta:set FT->\bar R.
Hypotheses (hBeta:is_measure beta) (hBetaRadon:is_radon_measure beta).
Local Notation lambda:=(@CartesianCurrentMeasure.value R n n Full Full alpha beta hAlpha hBeta).
Local Notation hLambda:=(@current_cartesian_measure_is_measure R n n Full Full alpha beta hAlpha hBeta).
Local Notation hLambdaRadon:=(@current_cartesian_measure_radon R n n Full Full hFull hFull
  alpha beta hAlpha hBeta hAlphaRadon hBetaRadon).
Variable w:X->R^o.
Hypothesis hW:norm_class_zero (N n) (fun t:R^o=>`|t|) Full w.
Hypothesis hPositive:forall z,0<=w z.
Variable r:R.
Hypothesis hOff:forall z,r<N n z->w z= 0.
Local Notation W:=(fun y:CT=>w (p (set_val y))).

(** Source for [euclidean_kernel_product_weight_continuous]:
    the original compact scalar translation weight is
    continuous on the actual original product domain,
    supporting the averaged variation in 4.1.18, p. 375. *)
Theorem euclidean_kernel_product_weight_continuous:continuous W.
Proof.
pose firstActual(y:CT):FT:=exist _ (p (set_val y)) (mem_set Logic.I).
have hFirst:continuous firstActual.
  apply:(@set_type_continuous_into XT Full CT firstActual).
  have hP:continuous (fun y:YT=>(p y:XT)).
    apply:norm_bounded_linear_continuous.
    exact:(@norm_finite_linear_bounded R Y X (N (n+n)%N) (N n)
      (hN (n+n)%N) (hN n) (n+n)%N (@coordinate_basis R (n+n)%N)
      (@coordinate_basisP R (n+n)%N) p).
  move=>y;exact:(continuous_comp (@set_type_val_continuous YT AB y) (hP (set_val y))).
have hScalar:=@norm_class_zero_scalar_restriction_continuous R X (N n) (hN n) Full w hW.
move=>y;exact:(continuous_comp (hFirst y) (hScalar (firstActual y))).
Qed.
Local Notation hWeight:=euclidean_kernel_product_weight_continuous.
Local Notation hWeightPositive:=(fun y:CT=>hPositive (p (set_val y))).
Local Notation hMeas:=(@continuous_radon_density_measurable R CT lambda hLambda hLambdaRadon
  W hWeight).
Local Notation hNonnegative:=(@continuous_radon_density_nonnegative R CT lambda hLambda
  W hWeightPositive).

(** Source for [euclidean_kernel_product_density]: the
    earlier density-measure construction applied to
    w(z) d(Lebesgue x beta)(z,x), supporting the
    original existence proof in 4.1.18, p. 375. *)
Definition euclidean_kernel_product_density:set CT->\bar R:=
  measure_with_density lambda (real_total_integrand W).
Local Notation gamma:=euclidean_kernel_product_density.

(** Source for [euclidean_kernel_product_density_laws]:
    the original continuous nonnegative density gives
    a Radon measure, without a finite total spatial
    mass hypothesis, supporting 4.1.18, p. 375. *)
Theorem euclidean_kernel_product_density_laws:
  is_measure gamma /\is_radon_measure gamma.
Proof.
split;first exact:(@measure_with_density_is_measure R CT lambda hLambda _ hNonnegative).
have[C [O [hC [hO [hOC [hCover hOpenCover]]]]]]:=
  @smooth_domain_compact_open_cover R Y (N (n+n)%N) (hN (n+n)%N)
    (n+n)%N (@coordinate_basis R (n+n)%N) (@coordinate_basisP R (n+n)%N) AB hAB.
exact:(@continuous_radon_density_radon R CT lambda hLambda hLambdaRadon
  W hWeight hWeightPositive C O hC hO hOC hCover hOpenCover).
Qed.

(** Source for [euclidean_kernel_product_density_carried]:
    the density measure is carried by the original
    closed translation-parameter ball, supporting
    4.1.18, p. 375. The spatial factor remains
    unrestricted, and radius zero is allowed. *)
Theorem euclidean_kernel_product_density_carried:
  gamma (~` (@euclidean_parameter_strip R n r))= 0%E.
Proof.
have hZero:=@finite_real_density_zero_locus_null R CT lambda gamma hLambda W
  (measure_with_density_laws lambda (real_total_integrand W)).
apply/eqP;rewrite eq_le (measure_nonnegative euclidean_kernel_product_density_laws.1 _) andbT.
rewrite -hZero.
apply:(@measure_mono R CT gamma euclidean_kernel_product_density_laws.1)=>y hy.
apply:hOff.
rewrite ltNge;apply/negP=>hSmall;exact:hy hSmall.
Qed.

(** Source for [euclidean_kernel_radon_image]: the
    actual image of the weighted original product
    under (z,x) to x+z, used only to prove
    existence of the independently specified average
    in 4.1.18, p. 375. *)
Definition euclidean_kernel_radon_image:set XT->\bar R:=
  measure_pushforward (@euclidean_parameter_addition R n) gamma.
Local Notation nu:=euclidean_kernel_radon_image.

(** Source for [euclidean_kernel_radon_image_laws]: the
    original averaged translated measure is Radon.
    Properness is required only on its bounded
    parameter carrying set, supporting 4.1.18, p. 375. *)
Theorem euclidean_kernel_radon_image_laws:
  is_measure nu /\is_radon_measure nu.
Proof.
split;first exact:measure_pushforward_is_measure euclidean_kernel_product_density_laws.1.
exact:(@carried_proper_radon_pushforward R CT XT gamma
  euclidean_kernel_product_density_laws.1 euclidean_kernel_product_density_laws.2
  (@euclidean_parameter_strip R n r) euclidean_kernel_product_density_carried
  (@euclidean_parameter_addition R n) (@euclidean_parameter_addition_continuous R n)
  (@metric_hausdorff R XT)
  (@finite_norm_locally_compact R X n (@coordinate_basis R n) (@coordinate_basisP R n)
    (N n) (hN n))
  (@euclidean_parameter_addition_strip_proper R n r)).
Qed.

(** Source for [euclidean_kernel_radon_image_compact_integral]:
    a positive compact test integrates against the
    original weighted product before its image is
    taken, by 2.4.10 and 2.4.18, supporting
    the translated-measure integral in 4.1.18, p. 375. *)
Theorem euclidean_kernel_radon_image_compact_integral f:
  positive_function_lattice (@compactly_supported_continuous_functions R XT) f ->
  is_measure_integral lambda
    (real_total_integrand (fun y:CT=>
      f (@euclidean_parameter_addition R n y)*W y))
    (@radon_positive_compact_integral R XT nu
      euclidean_kernel_radon_image_laws.1 euclidean_kernel_radon_image_laws.2 f)%:E.
Proof.
move=>hF.
exact:(@radon_weighted_pushforward_compact_integral R CT XT lambda gamma
  hLambda hLambdaRadon euclidean_kernel_product_density_laws.1
  euclidean_kernel_product_density_laws.2 W (@euclidean_parameter_addition R n)
  (measure_with_density_laws lambda (real_total_integrand W)) hMeas hNonnegative
  (@euclidean_parameter_addition_continuous R n)
  euclidean_kernel_radon_image_laws.1 euclidean_kernel_radon_image_laws.2 f hF).
Qed.
End EuclideanKernelProductDensity.
