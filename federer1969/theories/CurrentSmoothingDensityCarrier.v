(** Federer (1969), 4.1.18, pp. 375–376: the
    actual smooth multivector density of T_epsilon vanishes
    outside the original closed epsilon tube of spt T.
    Use the literal translated-kernel action from 4.1.2,
    p. 347, and the earlier test annihilation law.
    This pointwise assertion retains empty support and
    every exterior degree without a mass premise. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading AlternatingForms AlternatingPairing CurrentCoefficientNorms
  CurrentSpaces CurrentVectorSpaces CurrentMultivectorDual MultivectorDualSealed
  ContinuousDualUP CurrentSupportGeometry CurrentSupportAgreement
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation
  TranslatedKernelTestSealed TranslatedKernelTestBallSupport
  SmoothingKernelUP SmoothingDilationUP SmoothingDilationSmooth SmoothingDilationNonzeroRadius
  EuclideanClosedSupportTube VectorSetSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DensityCarrier.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation Y:=(A_m X R^o m).
Local Notation NY:=(@current_form_comass R h2 n m).
Local Notation hNY:=(@current_form_comass_real_norm R h2 n m).
Local Notation E:=(@current_smooth_space R h2 n Full hFull m).
Local Notation ev:=(@current_smooth_value R h2 n Full hFull m).
Local Notation hE:=(@current_smooth_space_laws R h2 n Full hFull m).
Local Notation V:=(@current_vector_smooth_space R h2 n Full hFull m).
Local Notation vv:=(@current_vector_smooth_value R h2 n Full hFull m).
Local Notation dual:=(@MultivectorDual.evaluation R X m).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.
Local Notation hKernel:=(@smoothing_dilation_smooth R n phi hPhi family hFamily epsilon hEpsilon).
Local Notation hOff:=(@smoothing_dilation_zero_beyond_radius R n phi family hPhi hFamily epsilon hEpsilon).
Local Notation B:=(@TranslatedKernelTest.value R n Y NY hNY E ev hE
  (family epsilon) hKernel epsilon hOff).
Local Notation hB:=(@TranslatedKernelTest.laws R n Y NY hNY E ev hE
  (family epsilon) hKernel epsilon hOff).
Variable T:@current_space R h2 n Full hFull m.
Local Notation action:=(@current_value R h2 n Full hFull m).
Local Notation Support:=(@current_support R h2 n Full hFull m T).

(** Source for [current_smoothing_density_zero_off_tube]:
    the original smooth coefficient field used in
    the representation iteration has the same literal
    closed-tube carrier as T_epsilon, Federer 4.1.18,
    pp. 375–376. Neither compactness nor finite
    mass of the input T is required for this
    exact pointwise zero assertion. *)
Theorem current_smoothing_density_zero_off_tube (xi:V):
  (forall z theta,pairing (vv xi z) theta=action T (B z theta))->
  forall z,~@euclidean_closed_support_tube R n Support epsilon z->vv xi z=0.
Proof.
move=>hPairing z hOutside.
apply:(continuous_dual_injective (@current_multivector_continuous_dual R h2 n m)).
apply:hom_ext=>theta.
rewrite (lin0 (hom_linear dual)).
change (dual (vv xi z) theta=0).
rewrite MultivectorDual.laws hPairing.
apply:(@current_test_disjoint_support_zero R h2 n m Full hFull T (B z theta))
  =>x hSupport hTest.
have hBall:=@translated_kernel_test_ball_support R n Y NY hNY E ev hE
  (family epsilon) epsilon B hOff hB z theta x hTest.
apply:hOutside.
apply/vector_set_sum_membership;exists x,(z-x);split;first exact:hSupport.
split.
- change (NX (z-x)<=epsilon).
  rewrite (real_seminorm_subtract hNX.1);exact:hBall.
- by rewrite addrC subrK.
Qed.
End DensityCarrier.
