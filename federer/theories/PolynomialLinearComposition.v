(** Supporting polynomial coefficient slices in Federer (1969), 2.6.5, p.
    120, from the symmetric-form definition in 1.10.4, pp. 45–47, and
    induced maps in 1.10.1, p. 44. These supporting composition laws work
    over every field and include degree zero. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SymmetricForms SymmetricFormDual SymmetricFormPostcompose
  HomogeneousPolynomialFunctions PolynomialFunctions PolynomialRepresentations PolynomialDiagonalNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [sform_polynomial_precompose]: supporting
    compatibility of 1.10.1, p. 44, with the polynomial
    evaluation of 1.10.4, p. 45, for Federer 2.6.5,
    p. 120: linear changes of the input preserve homogeneous degree. *)
Lemma sform_polynomial_precompose (K : fieldType) (U V W : lmodType K)
    (g : {linear U -> V}) m (f : S_m V W m) x :
  sform_polynomial_value (S_m_dual g f) x = sform_polynomial_value f (g x).
Proof.
rewrite !sform_polynomial_diagonal_value S_m_dualE.
congr (_ *: f _); apply: eq_from_tnth=> i.
by rewrite tnth_map !tnth_mktuple.
Qed.

(** Source for [sform_polynomial_postcompose]: supporting
    scalarisation of the coefficient forms of Federer 1.10.4,
    p. 46, for the polynomial slices in 2.6.5, p. 120. *)
Lemma sform_polynomial_postcompose (K : fieldType) (V W Z : lmodType K)
    (g : {linear W -> Z}) m (f : S_m V W m) x :
  sform_polynomial_value (symmetric_form_postcompose g f) x = g (sform_polynomial_value f x).
Proof. by rewrite !sform_polynomial_diagonal_value symmetric_form_postcomposeE linearZ. Qed.

(** Source for [polynomial_linear_precompose]: supporting
    restriction of a polynomial to a linear subspace in the
    induction of Federer 2.6.5, p. 120, directly from
    the finite representation of 1.10.4, p. 46. *)
Lemma polynomial_linear_precompose (K : fieldType) (U V W : lmodType K)
    (g : {linear U -> V}) (P : V -> W) :
  is_polynomial_function P -> is_polynomial_function (fun x => P (g x)).
Proof.
move/polynomial_finite_representation=> [N [f hf]].
apply/polynomial_finite_representation; exists N, (fun m => S_m_dual g (f m))=> x.
rewrite hf; apply: eq_bigr=> i _; exact: esym (sform_polynomial_precompose g (f i) x).
Qed.

(** Source for [polynomial_linear_postcompose]: supporting
    extraction of scalar coefficients in the induction of
    Federer 2.6.5, p. 120, from 1.10.4, p. 46. *)
Lemma polynomial_linear_postcompose (K : fieldType) (V W Z : lmodType K)
    (g : {linear W -> Z}) (P : V -> W) :
  is_polynomial_function P -> is_polynomial_function (fun x => g (P x)).
Proof.
move/polynomial_finite_representation=> [N [f hf]].
apply/polynomial_finite_representation; exists N, (fun m => symmetric_form_postcompose g (f m))=> x.
rewrite hf linear_sum; apply: eq_bigr=> i _; exact: esym (sform_polynomial_postcompose g (f i) x).
Qed.
