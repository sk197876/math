(** Federer (1969), 4.1.6, p. 352: an arbitrary
    coefficient vector space embeds in a unital algebra,
    and changing coefficients along an injection preserves
    the original forms. The proved tensor algebra of
    1.2.3 supplies the printed example. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
From Federer Require Import Hom AlgebraUP TensorAlgebra TensorPowers AlternatingForms FormCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [original_coefficient_algebra_embedding]:
    every coefficient vector space embeds in a unital
    algebra whose scalar multiples of the unit form a
    copy of the scalar field, Federer 4.1.6,
    p. 352. The existing original tensor algebra
    proves existence, including a zero coefficient space. *)
Theorem original_coefficient_algebra_embedding (K:fieldType) (W:lmodType K):
  exists (A:algebra K) (j:Hom W A),injective j /\
    injective (fun c:K=>c*:alg_one A).
Proof.
exists (tensor_algebra W),(hom_of_linear (tensor_generator_map W)); split.
- move=>x y h; apply:(@tensor_generator_injective K W).
  by rewrite -!tensor_generator_mapE.
- change (injective (@tensor_scalar K W)).
  exact:tensor_scalar_injective.
Qed.

(** Source for [original_form_coefficient_embedding]:
    changing coefficients through an injection embeds
    the entire original form space, supporting the
    arbitrary-coefficient expansion of Federer 4.1.6,
    p. 352. No finite-dimensional coefficient
    hypothesis is imposed. *)
Theorem original_form_coefficient_embedding (K:fieldType) (V W Z:lmodType K)
    (f:{linear W->Z}) m:
  injective f ->injective (@form_coefficients K V W Z f m).
Proof.
move=>hf a b h; apply:form_ext=>t; apply:hf.
have hValue:=congr1 (fun phi:A_m V Z m=>phi t) h.
by rewrite !form_coefficientsE in hValue.
Qed.
