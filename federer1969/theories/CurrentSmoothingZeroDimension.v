(** Federer (1969), 4.1.18, p. 374: in
    ambient dimension zero the original regularisation
    is the identity. This endpoint uses the unit
    integral of the kernel, not a nonempty coordinate
    choice or a negative-degree boundary.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms CurrentSpaces CurrentEvaluation CurrentCoefficientNorms
  CurrentCoefficientCompleteness SmoothFunctionSpaceLaws SmoothTestSpaces
  SmoothTestEvaluation LinearSubspaceRepresentationUP SmoothingKernelUP SmoothingDilationUP
  SmoothingPointwiseOscillation CurrentSmoothingOperators.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentSmoothingZeroDimension.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable m:nat.
Local Notation X:=(R_n R 0%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R 0%N)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation Y:=(A_m X R^o m).
Local Notation NY:=(@current_form_comass R h2 0%N m).
Local Notation hNY:=(@current_form_comass_real_norm R h2 0%N m).
Local Notation hY:=(@current_form_complete R h2 0%N m).
Local Notation E:=(@current_smooth_space R h2 0%N Full hFull m).
Local Notation ev:=(@current_smooth_value R h2 0%N Full hFull m).
Local Notation hE:=(@current_smooth_space_laws R h2 0%N Full hFull m).
Local Notation DT:=(@current_test_space R h2 0%N Full hFull m).
Local Notation C:=(@current_space R h2 0%N Full hFull m).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.

(** Source for [current_smooth_smoothing_zero_dimension]:
    the original convolution on R^0 has its original
    value, supporting the ambient-zero homotopy endpoint
    in Federer 4.1.18, p. 374. Every form
    degree is admitted, including zero forms. *)
Theorem current_smooth_smoothing_zero_dimension (omega:E):
  @current_smooth_smoothing R h2 0%N m phi family hPhi hFamily epsilon omega=omega.
Proof.
have hSingleton (x y:X):x=y.
  apply/ffunP=>i;have:=ltn_ord i;by rewrite ltn0.
apply:(smooth_function_extensional hE)=>x _.
apply:(@smoothing_pointwise_plateau R 0%N Y NY hNY hY phi hPhi family hFamily
  epsilon (ev omega)
  (ev (@current_smooth_smoothing R h2 0%N m phi family hPhi hFamily epsilon omega))
  hEpsilon (@current_smooth_smoothing_convolution R h2 0%N m phi family hPhi hFamily
    epsilon hEpsilon omega) x (ev omega x))=>z _.
by rewrite (hSingleton (x-z) x).
Qed.

(** Source for [current_test_smoothing_zero_dimension]:
    the actual compact test operator is also the
    identity in the ambient-zero case of 4.1.18,
    p. 374. *)
Theorem current_test_smoothing_zero_dimension (omega:DT):
  @current_test_smoothing R h2 0%N m phi family hPhi hFamily epsilon omega=omega.
Proof.
apply:(subspace_representation_injective (smooth_test_space_laws hE)).
rewrite (@current_test_smoothing_inclusion R h2 0%N m phi family hPhi hFamily
  epsilon hEpsilon omega).
exact:current_smooth_smoothing_zero_dimension.
Qed.

(** Source for [current_smoothing_zero_dimension]: the
    literal T_epsilon=T in ambient dimension zero,
    supporting Federer 4.1.18, p. 374. *)
Theorem current_smoothing_zero_dimension (T:C):
  @current_smoothing R h2 0%N m phi family hPhi hFamily T epsilon=T.
Proof.
apply:(@current_values_extensional R h2 0%N m Full hFull)=>omega.
by rewrite (@current_smoothing_action R h2 0%N m phi family hPhi hFamily
  T epsilon hEpsilon omega) current_test_smoothing_zero_dimension.
Qed.
End CurrentSmoothingZeroDimension.
