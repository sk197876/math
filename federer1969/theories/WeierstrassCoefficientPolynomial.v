(** Federer (1969), 3.4.6, p. 322: each actual
    split coefficient is a homogeneous polynomial of the
    original transverse degree j. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP SymmetricForms SymmetricFormDual PolynomialTaylorTerms
  HomogeneousPolynomialFunctions PolynomialLinearComposition AnalyticGermUP AnalyticGermCoefficientForms
  WeierstrassCoefficientUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [weierstrass_split_coefficient_homogeneous]:
    f_(i,j) has homogeneous degree j on ker(xi),
    3.4.6, p. 322. Contracting the actual
    derivative and applying the original linear inclusion
    proves this; polynomiality is not a defining hypothesis. *)
Theorem weierstrass_split_coefficient_homogeneous (R:realType) (X K:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (alpha:analytic_germ_space hNX (0:X))
    (v:X) (inclusion:Hom K X) i j (C:K->R):
  is_weierstrass_split_coefficient alpha v inclusion i j C ->
  @is_homogeneous_polynomial R K R^o j C.
Proof.
move=>hC.
have [F [hF _]]:=@analytic_germ_coefficient_forms_exists R X NX hNX 0 alpha.
exists (S_m_dual (hom_as_linear inclusion) (symmetric_taylor_term j (F (i+j)%N) v))=>z.
rewrite (hC (F (i+j)%N) (hF (i+j)%N) z) sform_polynomial_precompose.
reflexivity.
Qed.
