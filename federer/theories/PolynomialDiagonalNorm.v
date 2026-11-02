(** Federer (1969), 1.10.5, p. 48: the lower comparison
    m! ||P|| <= ||phi|| for P(x)=<x^m/m!,phi>. Source
    editions and comparison scope: PolynomialNormUP.v. The factorial
    normalization is kept exactly as in 1.10.4, p. 45.
    No finite-dimensional or boundedness hypothesis is imposed. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import Graded Hom HomogeneousHom SymmetricAlgebra SymmetricGrading
  SymmetricDividedMonomials SymmetricForms SymmetricFormWords SymmetricFormExtension
  SymmetricFormIsomorphism HomogeneousPolynomialFunctions RealNormUP
  PolynomialNorm SymmetricOperatorNormUP SymmetricOperatorNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [sform_polynomial_diagonal_value]: Federer 1.10.5,
    p. 48, the choice of phi in the polynomial norm comparison.
    The polynomial value is the diagonal form evaluation divided by m!. *)
Lemma sform_polynomial_diagonal_value (K : fieldType) (V W : lmodType K)
    m (f : S_m V W m) x :
  sform_polynomial_value f x = (m`!%:R : K)^-1 *: f [tuple x | i<m].
Proof.
rewrite /sform_polynomial_value /symmetric_divided_vector_power linearZ.
congr (_ *: _).
change (sform_extension f (symmetric_vector_power x m) = f [tuple x | i<m]).
rewrite /symmetric_vector_power sform_extensionE.
have ht : (nseq m x) = [seq x | i <- enum 'I_m].
  have hh (s : seq 'I_m) : [seq x | i <- s] = nseq (size s) x.
    by elim: s=> [|i s ih] //=; rewrite ih.
  by rewrite hh size_enum_ord.
rewrite ht.
change (sform_words f [tuple x | i<m] = f [tuple x | i<m]).
exact: sform_wordsE.
Qed.

(** Source for [polynomial_norm_form_lower_bound]: Federer
    1.10.5, p. 48, the first inequality in the displayed
    comparison m! ||P|| <= ||phi|| <= m^m ||P||. The first
    inequality follows by restricting the form to diagonal tuples.
    Degree zero and infinite norm values are included. *)
Theorem polynomial_norm_form_lower_bound (R : realType) (V W : lmodType R)
    (NV : V -> R) (NW : W -> R) (hV : is_real_seminorm NV) (hW : is_real_seminorm NW)
    m (f : S_m V W m) :
  (((m`!)%:R : R)%:E * polynomial_norm hV NW (sform_polynomial_value f) <=
    symmetric_operator_norm hV NW f)%E.
Proof.
have hp : (0 < ((m`!)%:R : R)) by rewrite ltr0n fact_gt0.
rewrite -(lee_pdivlMl _ _ hp).
apply: polynomial_norm_least=> x hx.
rewrite sform_polynomial_diagonal_value (real_seminorm_scale hW) normfV normr_nat EFinM.
apply: lee_wpmul2l; first by rewrite lee_fin invr_ge0 ler0n.
apply: symmetric_operator_norm_upper=> i; by rewrite tnth_mktuple.
Qed.
