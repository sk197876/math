(** Federer (1969), 3.4.12, p. 339: the original complex
    finite transverse remainder has every required directional derivative
    zero on its actual neighbourhood. Apply the existing line
    polynomial connection through the exact real scalar restriction. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP NormAnalyticUP
  ComplexWeierstrassTransverseUP ComplexWeierstrassRealRemainderLine NormAnalyticFiniteLineVanishing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Vanishing.
Variable R:realType.
Variables X K:lmodType (ComplexScalars.C R).
Variables (NX:X->R) (NK:K->R).
Variable hNX:is_real_norm (fun x:restricted_space (ComplexScalars.embed R) X=>NX x).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o).
Local Notation N:=(@complex_modulus R).
Local Notation hN:=(@complex_modulus_real_norm R).
Local Notation Z:=(fun i=>@ContinuousMultilinear.space R i XR CR NX N hNX hN).
Local Notation ev:=(fun i=>@ContinuousMultilinear.evaluation R i XR CR NX N hNX hN).
Local Notation ZN:=(fun i=>@ContinuousMultilinear.norm R i XR CR NX N hNX hN).

(** Source for [complex_weierstrass_finite_remainder_vanishing]: the
    actual all-point derivative condition in the complex extension
    of 3.4.6(1), p. 322, required by 3.4.12, p. 339. *)
Theorem complex_weierstrass_finite_remainder_vanishing v (xi:Hom X (ComplexScalars.C R)^o)
    (inclusion:Hom K X) (projection:Hom X K) k (D:nat->X->ComplexScalars.C R) (A:set X):
  is_complex_weierstrass_transverse_space NX NK v xi inclusion projection ->
  @norm_analytic R XR CR NX N hNX hN A
    (fun x=>\sum_(i<k) (xi x)^+i*D i (inclusion (projection x))) ->
  forall p,(k<=p)%N ->forall a,A a ->forall z:Z p,
    @has_norm_higher_differential R XR CR NX Z ev ZN setT
      (fun x=>\sum_(i<k) (xi x)^+i*D i (inclusion (projection x))) p a z ->
    @ev p [ffun _:'I_p=>v] z=0.
Proof.
move=>hSplit hf.
apply:(@norm_analytic_finite_line_high_derivative_zero R XR CR NX N hNX hN A
  (fun x=>\sum_(i<k) (xi x)^+i*D i (inclusion (projection x))) k v hf)=>a ha.
exact:(@complex_weierstrass_real_shifted_line R X K NX NK v xi inclusion projection k D hSplit a).
Qed.
End Vanishing.
