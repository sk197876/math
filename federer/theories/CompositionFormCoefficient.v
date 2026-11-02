(** Federer (1969), 3.1.11, p. 222: the symmetric
    form on the right of the general composition formula. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
From Federer Require Import Hom HomogeneousHom BoundedHom SymmetricAlgebra
  SymmetricForms SymmetricFormExtension SymmetricFormPostcompose SymmetricFormSum
  HomogeneousPolynomialFunctions SymmetricMultiIndices SymmetricDividedMonomials
  CompositionMultiIndices CompositionMultinomial CompositionFormMonomials.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section FormCoefficient.
Variable K : fieldType.
Variables X Y T : lmodType K.
Variable k : nat.
Variable phi : forall i, S_m X Y i.
Variable psi : forall j, S_m Y T j.

(** Source for [composition_differential_form_term]: the term
    D^(sum alpha)g composed with the inner symmetric-form
    monomial, divided by alpha!, in Federer 3.1.11, p. 222.
    The degree-p component makes the printed degree identification
    explicit without a hidden equality cast. *)
Definition composition_differential_form_term p (a : composition_indices k p) : S_m X T p :=
  let alpha := composition_indices_unbound a in
  ((symmetric_multi_factorial alpha)%:R)^-1*:
    symmetric_form_postcompose
      (hom_as_linear (sform_homogeneous (psi (symmetric_multi_degree alpha))))
      (sform_component p (composition_form_monomial phi alpha)).

(** Source for [composition_differential_form_coefficient]: the
    sum over S(p) in the displayed general composition formula,
    Federer 3.1.11, p. 222. *)
Definition composition_differential_form_coefficient p : S_m X T p :=
  \sum_(a : composition_indices k p) composition_differential_form_term a.

(** Source for [composition_differential_form_term_value]: the
    polynomial value of a term agrees with the monomial
    calculation of Federer 3.1.11, p. 222, including its
    factorial factor and the outer derivative's exact degree. *)
Lemma composition_differential_form_term_value (h0 : [pchar K]=i pred0) p
    (a : composition_indices k p) v :
  sform_polynomial_value (composition_differential_form_term a) v=
    composition_multinomial_term
      (fun i : 'I_k=>sform_polynomial_value (phi (val i).+1) v)
      (fun j=>(sform_homogeneous (psi j) : Hom (symmetric_space Y) T))
      (composition_indices_unbound a).
Proof.
rewrite /composition_differential_form_term linearZ.
change (((symmetric_multi_factorial (composition_indices_unbound a))%:R)^-1 *:
  sform_polynomial_value (symmetric_form_postcompose
    (hom_as_linear (sform_homogeneous (psi (symmetric_multi_degree (composition_indices_unbound a)))) )
    (sform_component p (composition_form_monomial phi (composition_indices_unbound a)))) v =
  composition_multinomial_term
    (fun i : 'I_k=>sform_polynomial_value (phi (val i).+1) v)
    (fun j=>(sform_homogeneous (psi j) : Hom (symmetric_space Y) T))
    (composition_indices_unbound a)).
rewrite composition_form_postcompose_value
  (@composition_form_monomial_component_value K X Y k phi h0
    (composition_indices_unbound a) p v (composition_indices_weight a)).
reflexivity.
Qed.

(** Source for [composition_differential_form_coefficient_value]:
    the homogeneous polynomial represented by the full right-hand
    form is the coefficient of weighted degree p computed
    from the jets, Federer 3.1.11, p. 222. *)
Lemma composition_differential_form_coefficient_value (h0 : [pchar K]=i pred0) p v :
  (p<=k)%N ->
  sform_polynomial_value (composition_differential_form_coefficient p) v=
    composition_weight_coefficient
      (fun i : 'I_k=>sform_polynomial_value (phi (val i).+1) v)
      (fun j=>(sform_homogeneous (psi j) : Hom (symmetric_space Y) T)) p.
Proof.
move=>hp.
rewrite composition_weight_coefficient_formula // /composition_differential_form_coefficient linear_sum.
have hv (I : finType) (F : I->X->T) : (\sum_i F i) v=\sum_i F i v.
  by elim/big_rec2: _=>[|i y g0 _ <-].
rewrite hv; apply: eq_bigr=>a _.
exact: composition_differential_form_term_value.
Qed.
End FormCoefficient.
