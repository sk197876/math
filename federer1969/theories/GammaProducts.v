(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import DualExterior.
From Federer Require Import TraceAlgebra TraceComponents TraceDefinition GammaPower AlgebraWordLaws.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.5, computation of the divided m-th power: each
    degree-one pure tensor has square zero; its ordered products are
    precisely the displayed omega_lambda tensor (exterior_power f)e_lambda. *)
Section GammaProducts.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variables V W : lmodType K.
Local Notation U := (alternating_unital_algebra h2 V (scalar_algebra K)).
Local Notation E := (exterior_algebra W).
Local Notation D := (A h2 V W).
Local Notation include := (@A_include K h2 V W).
(** Source for [Gamma_term]: Federer (1969), 1.4.5, p. 20, divided-power
    display and following natural isomorphisms. In words: The divided m-th
    power of Gamma(f) is the sum of omega_lambda tensored with the m-th
    exterior image of e_lambda, and equals Gamma of that exterior map.
    Definition or construction used to formalise this passage. *)
Definition Gamma_term (phi : A_m V K^o 1) (w : W) : D :=
  A_pure h2 phi (exterior_first_inclusion W w).
(** Source for [Gamma_term_include]: Federer (1969), 1.4.5, p. 20,
    divided-power display and following natural isomorphisms. In words: The
    divided m-th power of Gamma(f) is the sum of omega_lambda tensored with
    the m-th exterior image of e_lambda, and equals Gamma of that exterior
    map. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma Gamma_term_include phi w :
  include (Gamma_term phi w) = tensor_inj (form_include phi) (exterior_generator w).
Proof.
rewrite /Gamma_term A_pureE.
change (tensor_inj (form_include phi) (exterior_degree 1 (exterior_generator w)) =
  tensor_inj (form_include phi) (exterior_generator w)).
by rewrite exterior_generator_homogeneous.
Qed.
(** Source for [Gamma_term_square]: Federer (1969), 1.4.5, p. 20,
    divided-power display and following natural isomorphisms. In words: The
    divided m-th power of Gamma(f) is the sum of omega_lambda tensored with
    the m-th exterior image of e_lambda, and equals Gamma of that exterior
    map. Formalises the indicated part of the passage under the hypotheses
    in the statement below. *)
Lemma Gamma_term_square phi w : alg_mul D (Gamma_term phi w) (Gamma_term phi w) = 0.
Proof.
apply A_include_injective; rewrite algebra_map_mul !Gamma_term_include linear0.
change (@tensor_multiplication K U E (tensor_inj (form_include phi) (exterior_generator w))
  (tensor_inj (form_include phi) (exterior_generator w)) = 0).
rewrite tensor_multiplicationE.
change (tensor_inj (alg_mul U (form_include phi) (form_include phi))
  (wedge (exterior_generator w) (exterior_generator w)) = 0).
by rewrite exterior_generator_square tensor_inj0r.
Qed.
Variable I : choiceType.
Variable omega : I -> A_m V K^o 1.
Variable w : I -> W.
(** Source for [Gamma_product_include]: Federer (1969), 1.4.5, p. 20,
    divided-power display and following natural isomorphisms. In words: The
    divided m-th power of Gamma(f) is the sum of omega_lambda tensored with
    the m-th exterior image of e_lambda, and equals Gamma of that exterior
    map. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma Gamma_product_include (s : seq I) :
  include (word_eval (fun i => Gamma_term (omega i) (w i)) s) =
    tensor_inj (foldr (alg_mul U) (alg_one U) [seq form_include (omega i) | i <- s])
      (exterior_word [seq w i | i <- s]).
Proof.
rewrite algebra_map_word.
transitivity (@word_eval K I (algebra_tensor U E)
  (fun i => tensor_inj (form_include (omega i)) (exterior_generator (w i))) s).
- apply: word_eval_ext => i; exact: Gamma_term_include.
- by rewrite algebra_tensor_word word_eval_fold exterior_word_eval.
Qed.
End GammaProducts.

Section GammaLambdaProduct.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variables V W : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.
Variable omega : 'I_n -> A_m V K^o 1.
Variable f : Hom V W.
(** Source for [Gamma_Lambda_product]: Federer (1969), 1.4.5, p. 20,
    divided-power display and following natural isomorphisms. In words: The
    divided m-th power of Gamma(f) is the sum of omega_lambda tensored with
    the m-th exterior image of e_lambda, and equals Gamma of that exterior
    map. Formalises the indicated part of the passage under the hypotheses
    in the statement below. *)
Lemma Gamma_Lambda_product m (lambda : Lambda n m) :
  word_eval (fun i => Gamma_term h2 (omega i) (f (e i))) (val lambda) =
    A_pure h2 (omega_lambda h2 omega lambda)
      (exterior_power_map (hom_as_linear f) m (e_lambda e (val lambda))).
Proof.
apply A_include_injective; rewrite Gamma_product_include A_pureE omega_lambda_include.
congr tensor_inj.
change (exterior_word [seq f (e i) | i <- val lambda] =
  exterior_algebra_map (hom_as_linear f) (component_val (e_lambda e (val lambda)))).
by rewrite e_lambdaE exterior_algebra_map_word -map_comp.
Qed.
End GammaLambdaProduct.
