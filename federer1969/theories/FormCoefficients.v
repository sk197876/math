(** Federer (1969), 1.6.6, p. 26: conjugation and real and imaginary parts
    act on coefficients of forms. These degree-preserving maps support that
    passage and reuse the coefficient-algebra development of 1.4.4, p. 20.
    Source context are recorded in ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates CoefficientCoordinates
  AlternatingCoefficientMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Coefficients.
Variable K : fieldType.
Variables V W Z : lmodType K.
Variable f : {linear W -> Z}.

(** Source for [form_coefficients]: Federer 1.6.6, p. 26,
    conjugation and real and imaginary parts. Supporting construction
    applying a real linear map to the values of a form. *)
Definition form_coefficients m (a : A_m V W m) : A_m V Z m :=
  hom_to_form (hom_comp (hom_of_linear f) (form_to_hom a)).

(** Source for [form_coefficientsE]: Federer 1.6.6, p. 26,
    conjugation and real and imaginary parts. The map acts pointwise. *)
Lemma form_coefficientsE m (a : A_m V W m) t : form_coefficients a t = f (a t).
Proof. by rewrite /form_coefficients hom_to_formE hom_compE hom_of_linearE form_to_hom_tuple. Qed.

(** Source for [form_coefficients_include]: Federer 1.6.6,
    p. 26, the same coefficient operations on A^m and A^*.
    Supporting compatibility with the direct-sum inclusion. *)
Lemma form_coefficients_include m (a : A_m V W m) :
  form_include (form_coefficients a) = A_star_coefficients f (form_include a).
Proof.
apply: hom_finite_ext => x.
rewrite /form_coefficients form_include_hom_to_form hom_compE hom_of_linearE
  A_star_coefficientsE.
by rewrite -{2}(form_to_homK a) form_include_hom_to_form.
Qed.

(** Source for [form_coefficients_linear]: Federer 1.6.6,
    p. 26, real-linear coefficient operations on forms.
    Supporting linearity in a fixed degree. *)
Lemma form_coefficients_linear m : linear (@form_coefficients m).
Proof.
move=> c a b; apply: form_ext => t.
by rewrite form_coefficientsE !form_addE !form_scaleE !form_coefficientsE linearP.
Qed.
HB.instance Definition _ m := GRing.isLinear.Build K (A_m V W m) (A_m V Z m)
  *:%R (@form_coefficients m) (@form_coefficients_linear m).
End Coefficients.

Section Products.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variables W Z : algebra K.
Variable f : algebra_map W Z.

(** Source for [form_coefficients_wedge]: Federer 1.6.6,
    p. 26, conjugation automorphism of the alternating algebra.
    Supporting general statement: a coefficient algebra homomorphism
    commutes with the alternating product. *)
Lemma form_coefficients_wedge p q (a : A_m V W p) (b : A_m V W q) :
  form_coefficients f (form_wedge h2 (alg_bilinear W) a b) =
  form_wedge h2 (alg_bilinear Z) (form_coefficients f a) (form_coefficients f b).
Proof.
apply: (can_inj (@form_includeK K V Z (p+q))).
rewrite form_coefficients_include !form_wedge_include !form_coefficients_include.
exact: A_star_coefficients_mul.
Qed.
End Products.
