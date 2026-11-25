(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import DualExterior.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.5: multiplication of finite words commutes with
    algebra maps and with the ordinary product on a tensor product. *)
Section WordLaws.
Variable K : fieldType.
Variables B C : algebra K.
Variable I : choiceType.
(** Source for [word_eval_ext]: Federer (1969), 1.4.5, p. 20, divided-power
    display and following natural isomorphisms. In words: The divided m-th
    power of Gamma(f) is the sum of omega_lambda tensored with the m-th
    exterior image of e_lambda, and equals Gamma of that exterior map.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma word_eval_ext (a b : I -> B) : a =1 b -> forall s, word_eval a s = word_eval b s.
Proof. move=> h; elim=> [|i s ih] //=; by rewrite h ih. Qed.
(** Source for [word_eval_fold]: Federer (1969), 1.4.5, p. 20, divided-power
    display and following natural isomorphisms. In words: The divided m-th
    power of Gamma(f) is the sum of omega_lambda tensored with the m-th
    exterior image of e_lambda, and equals Gamma of that exterior map.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma word_eval_fold (a : I -> B) s :
  word_eval a s = foldr (alg_mul B) (alg_one B) [seq a i | i <- s].
Proof. by elim: s => [|i s ih] //=; rewrite ih. Qed.
(** Source for [algebra_map_word]: Federer (1969), 1.4.5, p. 20,
    divided-power display and following natural isomorphisms. In words: The
    divided m-th power of Gamma(f) is the sum of omega_lambda tensored with
    the m-th exterior image of e_lambda, and equals Gamma of that exterior
    map. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma algebra_map_word (F : algebra_map B C) (a : I -> B) s :
  F (word_eval a s) = word_eval (fun i => F (a i)) s.
Proof.
elim: s => [|i s ih]; first exact: algebra_map_one.
change (F (alg_mul B (a i) (word_eval a s)) =
  alg_mul C (F (a i)) (word_eval (fun j => F (a j)) s)).
by rewrite algebra_map_mul ih.
Qed.
(** Source for [algebra_tensor_word]: Federer (1969), 1.4.5, p. 20,
    divided-power display and following natural isomorphisms. In words: The
    divided m-th power of Gamma(f) is the sum of omega_lambda tensored with
    the m-th exterior image of e_lambda, and equals Gamma of that exterior
    map. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma algebra_tensor_word (a : I -> B) (b : I -> C) s :
  @word_eval K I (algebra_tensor B C) (fun i => tensor_inj (a i) (b i)) s =
  tensor_inj (word_eval a s) (word_eval b s).
Proof.
elim: s => [|i s ih] //=.
by rewrite ih tensor_multiplicationE.
Qed.
End WordLaws.
(** Source for [exterior_word_eval]: Federer (1969), 1.4.5, p. 20,
    divided-power display and following natural isomorphisms. In words: The
    divided m-th power of Gamma(f) is the sum of omega_lambda tensored with
    the m-th exterior image of e_lambda, and equals Gamma of that exterior
    map. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma exterior_word_eval (K : fieldType) (V : lmodType K)
    (I : choiceType) (w : I -> V) s :
  @word_eval K I (exterior_algebra V) (fun i => exterior_generator (w i)) s =
  exterior_word [seq w i | i <- s].
Proof.
elim: s => [|i s ih]; first by rewrite /= exterior_word_nil.
change (wedge (exterior_generator (w i))
  (@word_eval K I (exterior_algebra V) (fun j => exterior_generator (w j)) s) =
  exterior_word (w i :: [seq w j | j <- s])).
by rewrite exterior_word_cons ih.
Qed.
