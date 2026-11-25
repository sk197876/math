(** Federer (1969), 4.1.19, p. 377: both
    bounded measurable forms have their actual smooth
    convolutions. Total zero extension gives one common
    ambient presentation; its restriction to each valid
    interior locus retains the original U-valued integral. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import AlternatingForms RealNormUP NormMetric
  NormDifferentialUP NormBoundedLinearTopology NormRegularity NormClassOneUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain CurrentCoefficientNorms CurrentCoefficientCompleteness
  CompactContinuousVectorZeroExtension
  EuclideanOpenDomainMeasure EuclideanLebesgueDimensions
  EuclideanDistributionMeasureContext OpenSubspaceTotalZeroExtension
  FlatCochainRepresentationUP LocallyIntegrableVectorFieldUP
  LocallyBoundedMeasurableFieldIntegrability SmoothingKernelUP
  SmoothingDilationUP SmoothingDilationSmooth SmoothingDilationNonzeroRadius
  SmoothingConvolutionUP SmoothingConvolutionExistence
  CompactSmoothConvolutionSmoothness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section BoundedFormSmoothing.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n d : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation Y := (A_m X R^o d).
Local Notation NY := (@current_form_comass R h2 n d).
Local Notation hNY := (@current_form_comass_real_norm R h2 n d).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation UT := (current_domain R n U).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Local Notation hLeb := (euclidean_lebesgue_is_measure R n).
Variable phi : UT -> Y.
Local Notation extension := (@compact_vector_open_extension R XT U Y phi).

(** Source for [bounded_current_form_extension_locally_integrable]:
    the bounded measurable input of the smoothing
    clause in Federer 4.1.19, p. 377,
    has locally integrable norm after actual zero
    extension. No finite total Lebesgue measure or
    global compact support is needed. *)
Theorem bounded_current_form_extension_locally_integrable :
  @is_bounded_measurable_current_form R h2 n U d phi ->
  @is_locally_integrable_vector_field R X Y NX NY hNX hNY Leb extension.
Proof.
move=> [hMeas [c [hC hBound]]].
have hOpen : @open XT U.
  rewrite openE=> x hx.
  exact: (norm_domain_interior_neighbourhood hNX U x).1 (@hU x hx).
have hExtension := @open_subspace_total_zero_extension_measurable R XT U
  Leb hLeb (@euclidean_distribution_measure_open R n U hOpen)
  Y NY hNY phi hMeas.1.
apply: (@locally_bounded_measurable_field_locally_integrable R n Y NY hNY
  extension hExtension)=> K.
exists c; split; first exact: hC.
move=> x _; case: (pselect (U x))=> hx.
- pose a : UT := exist _ x (mem_set hx).
  change (is_true (NY (extension (set_val a))<=c)).
  rewrite compact_vector_open_extension_value; exact: hBound.
- rewrite (compact_vector_open_extension_outside _ hx)
    (real_seminorm_zero hNY.1); exact: hC.
Qed.

(** Source for [bounded_current_form_smoothing_exists]:
    the actual smooth Phi_epsilon*phi in
    Federer 4.1.19, p. 377, for
    every positive original radius. The finite
    coefficient space supplies exactly the Banach and
    separability hypotheses of the proved convolution theorem. *)
Theorem bounded_current_form_smoothing_exists
    (kernel : X -> R) (family : R -> X -> R)
    (epsilon : R) :
  is_smoothing_kernel kernel -> is_smoothing_dilation kernel family ->
  0<epsilon ->
  @is_bounded_measurable_current_form R h2 n U d phi ->
  exists g : X -> Y,
    is_smoothing_convolution hNY (family epsilon) extension g /\
    norm_class_all_orders hNX hNY (fun _ => True) g.
Proof.
move=> hKernel hFamily hEpsilon hPhi.
have hField := bounded_current_form_extension_locally_integrable hPhi.
have [g hG] := @smoothing_convolution_exists R n Y NY hNY
  (@current_form_complete R h2 n d) (@current_form_separable R h2 n d)
  kernel hKernel family hFamily epsilon hEpsilon extension hField.
exists g; split; first exact: hG.
exact: (@compact_smooth_convolution_smooth R n Y NY hNY
  (@current_form_complete R h2 n d) (@current_form_separable R h2 n d)
  extension hField (family epsilon) epsilon g
  (@smoothing_dilation_smooth R n kernel hKernel family hFamily epsilon hEpsilon)
  (@smoothing_dilation_zero_beyond_radius R n kernel family
    hKernel hFamily epsilon hEpsilon) hG).
Qed.
End BoundedFormSmoothing.
