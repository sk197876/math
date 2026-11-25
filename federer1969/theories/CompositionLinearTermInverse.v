(** Federer (1969), 3.1.24, p. 239: postcomposing
    the unique outer-linear composition term by the inverse
    first derivative recovers the highest inner differential. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import Hom HomogeneousHom BoundedHom SymmetricAlgebra SymmetricForms
  SymmetricFormExtension SymmetricFormPostcompose HomogeneousPolynomialFunctions
  SymmetricMultiIndices CompositionMultiIndices CompositionMultinomial CompositionFormMonomials CompositionFormCoefficient
  CompositionLinearMonomial CompositionLinearSymmetricMonomial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [composition_linear_term_left_inverse]: supporting
    the isolated D^p f in the inverse derivative formula of
    Federer 3.1.24, p. 239. If L is a left inverse
    of the outer first derivative, applying L to the unique
    outer-linear composition term gives the pth inner form.
    Equality of diagonal polynomials recovers equality of forms
    by the proved characteristic-zero polarization theorem. *)
Lemma composition_linear_term_left_inverse (K:fieldType) (h0:[pchar K]=i pred0)
    (X Y:lmodType K) p (phi:forall i,S_m X Y i) (psi:forall i,S_m Y X i)
    (L:Hom X Y) (a:composition_indices p p) :
  (forall y,L (sform_homogeneous (psi 1%N) (symmetric_generator y))=y) ->
  symmetric_multi_degree (composition_indices_unbound a)= 1%N ->
  symmetric_form_postcompose (hom_as_linear L)
    (@composition_differential_form_term K X Y X p phi psi p a)=phi p.
Proof.
move=>hL hd.
apply:(@sform_polynomial_injective K X Y p h0); apply:funext=>v.
rewrite composition_form_postcompose_value
  (@composition_differential_form_term_value K X Y X p phi psi h0 p a v)
  /composition_multinomial_term (composition_degree_one_factorial hd) invr1 scale1r hd.
rewrite (composition_degree_one_symmetric_monomial (fun i=>sform_polynomial_value (phi i) v) hd).
change (L (sform_homogeneous (psi 1%N) (symmetric_generator (sform_polynomial_value (phi p) v)))=
  sform_polynomial_value (phi p) v).
exact:hL.
Qed.
