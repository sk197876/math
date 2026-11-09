(** Federer (1969), 3.4.6, p. 322: existence and
    uniqueness of the original actual split Taylor coefficients. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP SymmetricForms PolynomialTaylorTerms HomogeneousPolynomialFunctions
  AnalyticGermUP AnalyticGermCoefficientForms WeierstrassCoefficientUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [weierstrass_split_coefficients_exist]: all
    original mixed coefficients exist on the actual transverse
    space, 3.4.6, p. 322. Actual derivative
    forms supply only local existence witnesses. *)
Theorem weierstrass_split_coefficients_exist (R:realType) (X K:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (alpha:analytic_germ_space hNX (0:X))
    (v:X) (inclusion:Hom K X):
  exists C:nat->nat->K->R,forall i j,
    is_weierstrass_split_coefficient alpha v inclusion i j (C i j).
Proof.
have [F [hF _]]:=@analytic_germ_coefficient_forms_exists R X NX hNX 0 alpha.
exists (fun i j z=>sform_polynomial_value (symmetric_taylor_term j (F (i+j)%N) v) (inclusion z)).
move=>i j G hG z.
have hGF:G=F (i+j)%N.
  apply:sform_ext=>t;by rewrite hG hF.
by rewrite hGF.
Qed.

(** Source for [weierstrass_split_coefficient_unique]: the
    original actual derivative germ determines each split
    coefficient function uniquely, 3.4.6, pp. 322–323. *)
Theorem weierstrass_split_coefficient_unique (R:realType) (X K:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (alpha:analytic_germ_space hNX (0:X))
    (v:X) (inclusion:Hom K X) i j (C D:K->R):
  is_weierstrass_split_coefficient alpha v inclusion i j C ->
  is_weierstrass_split_coefficient alpha v inclusion i j D ->C=1 D.
Proof.
move=>hC hD z.
have [F [hF _]]:=@analytic_germ_coefficient_forms_exists R X NX hNX 0 alpha.
by rewrite (hC (F (i+j)%N) (hF (i+j)%N) z) (hD (F (i+j)%N) (hF (i+j)%N) z).
Qed.
