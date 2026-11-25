(** Federer (1969), 4.1.19, p. 377: the
    original weak exterior equation is equivalent to
    commutation of every positive-radius smooth convolution
    on its original interior domain. Such actual
    convolution families exist for every bounded measurable
    pair, including empty U and all exterior degrees. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct AlternatingForms CurrentDomain CurrentCoefficientNorms
  CompactContinuousVectorZeroExtension FlatCochainRepresentationUP CurrentWeakExteriorPairUP
  BoundedCurrentFormSmoothing SmoothingKernelUP SmoothingDilationUP SmoothingConvolutionUP
  ClosedBallContainmentOpen ExteriorDerivativeUP CurrentWeakExteriorSmoothing
  CurrentSmoothingWeakExteriorConverse.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section SmoothingEquivalence.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation Y d := (A_m X R^o d).
Local Notation YN d := (@current_form_comass R h2 n d).
Local Notation hYN d := (@current_form_comass_real_norm R h2 n d).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation UT := (current_domain R n U).
Variables (phi : UT -> Y m) (psi : UT -> Y m.+1).
Hypothesis hPhi : @is_bounded_measurable_current_form R h2 n U m phi.
Hypothesis hPsi : @is_bounded_measurable_current_form R h2 n U m.+1 psi.
Local Notation extensionPhi := (@compact_vector_open_extension R XT U (Y m) phi).
Local Notation extensionPsi := (@compact_vector_open_extension R XT U (Y m.+1) psi).
Variables (kernel : X -> R) (family : R -> X -> R).
Hypothesis hKernel : is_smoothing_kernel kernel.
Hypothesis hFamily : is_smoothing_dilation kernel family.

(** Source for [current_weak_exterior_smoothing_iff]:
    the full smoothing equivalence in Federer
    4.1.19, p. 377, for every actual
    family of the two ordinary coefficient convolutions.
    The differential equation is required only where
    the original closed kernel ball lies in U. *)
Theorem current_weak_exterior_smoothing_iff
    (g : R -> X -> Y m) (h : R -> X -> Y m.+1) :
  (forall epsilon, 0<epsilon ->
    is_smoothing_convolution (hYN m) (family epsilon) extensionPhi (g epsilon)) ->
  (forall epsilon, 0<epsilon ->
    is_smoothing_convolution (hYN m.+1) (family epsilon) extensionPsi (h epsilon)) ->
  (@is_weak_current_exterior_pair R h2 n m U hU phi psi <->
    forall epsilon, 0<epsilon -> forall z,
      norm_closed_ball_containment U epsilon z ->
      has_exterior_derivative NX (YN m) U (g epsilon) z (h epsilon z)).
Proof.
move=> hG hH; split.
- move=> hWeak epsilon hEpsilon.
  exact: (@current_weak_exterior_smoothing R h2 n m U hU phi psi
    kernel family hKernel hFamily epsilon hEpsilon (g epsilon) (h epsilon)
    hPhi hPsi hWeak (@hG epsilon hEpsilon) (@hH epsilon hEpsilon)).
- exact: (@current_smoothing_weak_exterior_converse R h2 n m U hU phi psi
    kernel family hKernel hFamily g h hPhi hPsi hG hH).
Qed.

(** Source for [current_weak_exterior_smoothing_families_exist]:
    actual smooth convolutions for the equivalent
    criterion in Federer 4.1.19, p. 377,
    are obtained internally from the original bounded
    measurable pair. No new extension, smoothness or
    convergence premise is imposed on a caller. *)
Theorem current_weak_exterior_smoothing_families_exist :
  exists g : R -> X -> Y m, exists h : R -> X -> Y m.+1,
    (forall epsilon, 0<epsilon ->
      is_smoothing_convolution (hYN m) (family epsilon) extensionPhi (g epsilon) /\
      is_smoothing_convolution (hYN m.+1) (family epsilon) extensionPsi (h epsilon) /\
      norm_class_all_orders hNX (hYN m) (fun _ => True) (g epsilon) /\
      norm_class_all_orders hNX (hYN m.+1) (fun _ => True) (h epsilon)) /\
    (@is_weak_current_exterior_pair R h2 n m U hU phi psi <->
      forall epsilon, 0<epsilon -> forall z,
        norm_closed_ball_containment U epsilon z ->
        has_exterior_derivative NX (YN m) U (g epsilon) z (h epsilon z)).
Proof.
have hEachG (epsilon : R) : exists g : X -> Y m, 0<epsilon ->
    is_smoothing_convolution (hYN m) (family epsilon) extensionPhi g /\
    norm_class_all_orders hNX (hYN m) (fun _ => True) g.
  case: (pselect (0<epsilon))=> hEpsilon.
  - have [g hG] := @bounded_current_form_smoothing_exists R h2 n m U hU phi
      kernel family epsilon hKernel hFamily hEpsilon hPhi.
    by exists g.
  - exists (fun _ => 0); by move=> hPositive; exfalso; exact: hEpsilon hPositive.
have hEachH (epsilon : R) : exists h : X -> Y m.+1, 0<epsilon ->
    is_smoothing_convolution (hYN m.+1) (family epsilon) extensionPsi h /\
    norm_class_all_orders hNX (hYN m.+1) (fun _ => True) h.
  case: (pselect (0<epsilon))=> hEpsilon.
  - have [h hH] := @bounded_current_form_smoothing_exists R h2 n m.+1 U hU psi
      kernel family epsilon hKernel hFamily hEpsilon hPsi.
    by exists h.
  - exists (fun _ => 0); by move=> hPositive; exfalso; exact: hEpsilon hPositive.
have [g hG] := choice hEachG.
have [h hH] := choice hEachH.
exists g,h; split.
- move=> epsilon hEpsilon; split; first exact: (@hG epsilon hEpsilon).1.
  split; first exact: (@hH epsilon hEpsilon).1.
  split; [exact: (@hG epsilon hEpsilon).2 | exact: (@hH epsilon hEpsilon).2].
- exact: (@current_weak_exterior_smoothing_iff g h
    (fun epsilon he => (@hG epsilon he).1)
    (fun epsilon he => (@hH epsilon he).1)).
Qed.
End SmoothingEquivalence.
