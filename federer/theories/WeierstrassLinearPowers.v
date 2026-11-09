(** Federer (1969), 3.4.6, p. 323: powers of
    the original functional and linear pullbacks of transverse
    polynomials retain their printed homogeneous degrees. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom SymmetricForms SymmetricFormDual SymmetricFunctionalProduct
  HomogeneousPolynomialFunctions PolynomialDiagonalNorm PolynomialLinearComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_functional_power_homogeneous]:
    xi^i is an actual homogeneous degree-i polynomial,
    including i=0, in the grouping of 3.4.6, p. 323. *)
Lemma weierstrass_functional_power_homogeneous (R:realType) (X:lmodType R)
    (xi:Hom X R^o) m:
  @is_homogeneous_polynomial R X R^o m (fun x=>(xi x)^+m).
Proof.
pose F:=(m`!)%:R*:symmetric_functional_product_form (hom_as_linear xi) m.
exists F=>x.
rewrite sform_polynomial_diagonal_value /F sform_scaleE symmetric_functional_product_formE.
have hProduct:(\prod_(i<m) (hom_as_linear xi) (tnth [tuple x | j<m] i))=(xi x)^+m.
  under eq_bigr do rewrite tnth_mktuple hom_as_linearE.
  by rewrite prodr_const card_ord.
rewrite hProduct.
change ((xi x)^+m=((m`!)%:R:R)^-1*((m`!)%:R*(xi x)^+m)).
rewrite mulrA mulVf ?mul1r //.
by rewrite pnatr_eq0 -lt0n fact_gt0.
Qed.

(** Source for [weierstrass_homogeneous_pullback]: the
    original transverse projection preserves homogeneous degree
    under composition, supporting 3.4.6, p. 323. *)
Lemma weierstrass_homogeneous_pullback (R:realType) (X K:lmodType R)
    (projection:Hom X K) j (P:K->R):
  @is_homogeneous_polynomial R K R^o j P ->
  @is_homogeneous_polynomial R X R^o j (fun x=>P (projection x)).
Proof.
move=>[F hF].
exists (S_m_dual (hom_as_linear projection) F)=>x.
rewrite sform_polynomial_precompose hom_as_linearE.
exact:hF.
Qed.
