(** Federer (1969), 3.4.6(2), p. 322: all
    original preparation germs are uniquely determined. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP AnalyticGermUP AnalyticGermRing
  WeierstrassRegularUP WeierstrassTransverseUP WeierstrassDivisionUP WeierstrassDivisionWithTransverse
  WeierstrassFunctionalPower WeierstrassPreparationUP WeierstrassPolynomialRemainder WeierstrassPolynomialGermUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_preparation_with_transverse_unique]:
    quotient, monic polynomial and every transverse
    coefficient germ are uniquely determined by the original
    v, xi and phi, 3.4.6(2), p. 322.
    Every candidate gives an actual division of xi^k;
    proved division uniqueness identifies Q and W, and
    local finite coefficient uniqueness identifies every Wi. *)
Theorem weierstrass_preparation_with_transverse_unique (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (hNK:is_real_norm NK)
    (v:X) (xi:Hom X R^o) (inclusion:Hom K X) (projection:Hom X K) k
    (Phi Q W Q' W':@analytic_germ_ring R X NX hNX 0)
    (Wi Wi':'I_k->@analytic_germ_ring R K NK hNK 0):
  is_weierstrass_transverse_space NX NK v xi inclusion projection ->
  norm_bounded_linear NX (fun t:R^o=>`|t|) xi ->is_weierstrass_regular_germ Phi k v ->
  @is_weierstrass_preparation R X K NX NK hNX hNK xi projection k Phi Q W Wi ->
  @is_weierstrass_preparation R X K NX NK hNX hNK xi projection k Phi Q' W' Wi' ->
  Q=Q' /\W=W' /\forall i,Wi i=Wi' i.
Proof.
move=>hSplit hXi hRegular hPreparation hPreparation'.
have [power [hPowerValues hPower]]:=@weierstrass_functional_power_representative R X NX hNX xi k hXi.
pose Psi:@analytic_germ_ring R X NX hNX 0:=analytic_germ power.
have hR:=@weierstrass_polynomial_remainder R X K NX NK hNX hNK v xi inclusion projection k
  power W Wi hSplit hPowerValues hPower (weierstrass_preparation_polynomial hPreparation).
have hR':=@weierstrass_polynomial_remainder R X K NX NK hNX hNK v xi inclusion projection k
  power W' Wi' hSplit hPowerValues hPower (weierstrass_preparation_polynomial hPreparation').
have hDivision:@is_weierstrass_division R X NX hNX k v Phi Psi Q (Psi-W).
  constructor;last exact:hR.
  by rewrite (weierstrass_preparation_identity hPreparation) addrC subrK.
have hDivision':@is_weierstrass_division R X NX hNX k v Phi Psi Q' (Psi-W').
  constructor;last exact:hR'.
  by rewrite (weierstrass_preparation_identity hPreparation') addrC subrK.
have [baseQ [baseT [_ hUnique]]]:=@weierstrass_division_with_transverse R X K NX NK hNX hNK
  v xi inclusion projection k Phi Psi hSplit hXi hRegular.
have hEqualQ:Q=Q':=etrans (hUnique Q (Psi-W) hDivision).1 (esym (hUnique Q' (Psi-W') hDivision').1).
have hEqualW:W=W'.
  by rewrite -(weierstrass_preparation_identity hPreparation)
    -(weierstrass_preparation_identity hPreparation') hEqualQ.
split;first exact:hEqualQ.
split;first exact:hEqualW.
exact:(@weierstrass_polynomial_germ_coefficients_unique R X K NX NK hNX hNK v xi inclusion projection k
  W W' Wi Wi' hSplit (weierstrass_preparation_polynomial hPreparation)
  (weierstrass_preparation_polynomial hPreparation') hEqualW).
Qed.
