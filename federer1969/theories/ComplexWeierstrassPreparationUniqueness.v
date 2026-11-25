(** Federer (1969), 3.4.12, p. 339, extending 3.4.6(2), p. 322: all
    original preparation germs are uniquely determined. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus HolomorphicLinear Hom RealNormUP NormDifferentialUP HolomorphicGermUP HolomorphicGermRing
  ComplexWeierstrassRegularUP ComplexWeierstrassTransverseUP ComplexWeierstrassDivisionUP ComplexWeierstrassDivisionWithTransverse
  ComplexWeierstrassFunctionalPower ComplexWeierstrassPreparationUP ComplexWeierstrassPolynomialRemainder ComplexWeierstrassPolynomialGermUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [complex_weierstrass_preparation_with_transverse_unique]:
    quotient, monic polynomial and every transverse
    coefficient germ are uniquely determined by the original
    v, xi and phi, 3.4.6(2), p. 322.
    Every candidate gives an actual division of xi^k;
    proved division uniqueness identifies Q and W, and
    local finite coefficient uniqueness identifies every Wi. *)
Theorem complex_weierstrass_preparation_with_transverse_unique (R:realType) (X K:lmodType (ComplexScalars.C R))
    (NX:X->R) (NK:K->R) (hNX:is_complex_norm NX) (hNK:is_complex_norm NK)
    (v:X) (xi:Hom X (ComplexScalars.C R)^o) (inclusion:Hom K X) (projection:Hom X K) k
    (Phi Q W Q' W':@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0)
    (Wi Wi':'I_k->@holomorphic_germ_ring R K NK (complex_norm_real hNK) 0):
  is_complex_weierstrass_transverse_space NX NK v xi inclusion projection ->
  @norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (complex_hom_real xi) ->is_complex_weierstrass_regular_germ hNX Phi k v ->
  @is_complex_weierstrass_preparation R X K NX NK (complex_norm_real hNX) (complex_norm_real hNK) xi projection k Phi Q W Wi ->
  @is_complex_weierstrass_preparation R X K NX NK (complex_norm_real hNX) (complex_norm_real hNK) xi projection k Phi Q' W' Wi' ->
  Q=Q' /\W=W' /\forall i,Wi i=Wi' i.
Proof.
move=>hSplit hXi hRegular hPreparation hPreparation'.
have [power [hPowerValues hPower]]:=@complex_weierstrass_functional_power_representative R X NX hNX xi k hXi.
pose Psi:@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0:=holomorphic_germ power.
have hR:=@complex_weierstrass_polynomial_remainder R X K NX NK (complex_norm_real hNX) (complex_norm_real hNK) v xi inclusion projection k
  power W Wi hSplit hPowerValues hPower (complex_weierstrass_preparation_polynomial hPreparation).
have hR':=@complex_weierstrass_polynomial_remainder R X K NX NK (complex_norm_real hNX) (complex_norm_real hNK) v xi inclusion projection k
  power W' Wi' hSplit hPowerValues hPower (complex_weierstrass_preparation_polynomial hPreparation').
have hDivision:@is_complex_weierstrass_division R X NX (complex_norm_real hNX) k v Phi Psi Q (Psi-W).
  constructor;last exact:hR.
  by rewrite (complex_weierstrass_preparation_identity hPreparation) addrC subrK.
have hDivision':@is_complex_weierstrass_division R X NX (complex_norm_real hNX) k v Phi Psi Q' (Psi-W').
  constructor;last exact:hR'.
  by rewrite (complex_weierstrass_preparation_identity hPreparation') addrC subrK.
have [baseQ [baseT [_ hUnique]]]:=@complex_weierstrass_division_with_transverse R X K NX NK hNX hNK
  v xi inclusion projection k Phi Psi hSplit hXi hRegular.
have hEqualQ:Q=Q':=etrans (hUnique Q (Psi-W) hDivision).1 (esym (hUnique Q' (Psi-W') hDivision').1).
have hEqualW:W=W'.
  by rewrite -(complex_weierstrass_preparation_identity hPreparation)
    -(complex_weierstrass_preparation_identity hPreparation') hEqualQ.
split;first exact:hEqualQ.
split;first exact:hEqualW.
exact:(@complex_weierstrass_polynomial_germ_coefficients_unique R X K NX NK hNX hNK v xi inclusion projection k
  W W' Wi Wi' hSplit (complex_weierstrass_preparation_polynomial hPreparation)
  (complex_weierstrass_preparation_polynomial hPreparation') hEqualW).
Qed.
