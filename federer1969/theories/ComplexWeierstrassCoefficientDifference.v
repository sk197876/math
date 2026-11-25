(** Federer (1969), 3.4.12, p. 339: subtraction of actual
    complex germs subtracts their original mixed coefficients.
    Apply the proved actual jet arithmetic before evaluation. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexModulus ComplexScalarNorm ContinuousMultilinearUP ContinuousMultilinearSealed
  HolomorphicGermUP HolomorphicGermSealed HolomorphicGermJetArithmetic HolomorphicGermJetZeroNegate
  ComplexWeierstrassCoefficientUP ComplexWeierstrassCoefficientValue.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [complex_weierstrass_split_coefficient_difference]: the
    exact original remainder coefficients in the extension of
    3.4.6, p. 323, required by 3.4.12, p. 339. *)
Lemma complex_weierstrass_split_coefficient_difference (R:realType)
    (X K:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:is_complex_norm NX)
    (alpha beta:holomorphic_germ_space (complex_norm_real hNX) (0:X))
    (v:X) (inclusion:Hom K X) i j (A B T:K->ComplexScalars.C R):
  is_complex_weierstrass_split_coefficient hNX alpha v inclusion i j A ->
  is_complex_weierstrass_split_coefficient hNX beta v inclusion i j B ->
  is_complex_weierstrass_split_coefficient hNX
    (@HolomorphicGerms.add R X NX (complex_norm_real hNX) 0 alpha
      (@HolomorphicGerms.opp R X NX (complex_norm_real hNX) 0 beta)) v inclusion i j T ->
  forall z,T z=A z-B z.
Proof.
move=>hA hB hT z.
rewrite (complex_weierstrass_split_coefficient_value hT z)
  holomorphic_germ_jet_add holomorphic_germ_jet_negate.
have hEvaluation:forall (L:Hom (@ContinuousMultilinear.space R (i+j)%N
    (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
    NX (@complex_modulus R) (complex_norm_real hNX) (@complex_modulus_real_norm R))
    (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)) a b,
    L (a+ -b)=L a-L b.
  move=>L a b;exact:linearB.
rewrite hEvaluation mulrBr.
by rewrite -(complex_weierstrass_split_coefficient_value hA z)
  -(complex_weierstrass_split_coefficient_value hB z).
Qed.
