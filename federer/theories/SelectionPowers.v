(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlgebraUP Bilinear AlgebraTensor WordAlgebra ExteriorIndices ShuffleSums ExteriorExpansion.
From Federer Require Import AlgebraPowers.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.5, divided powers: index the square-free terms by
    Federer's Lambda(n,m). The recursive selection is only a device
    for proving that each increasing sequence occurs exactly once. *)
Section SelectionPowers.
Variable K : fieldType.
Variable B : algebra K.
Local Notation mul := (alg_mul B).
Local Notation one := (alg_one B).
(** Source for [selected_product]: Federer (1969), 1.4.5, p. 20,
    divided-power display and following natural isomorphisms. In words: The
    divided m-th power of Gamma(f) is the sum of omega_lambda tensored with
    the m-th exterior image of e_lambda, and equals Gamma of that exterior
    map. Definition or construction used to formalise this passage. *)
Definition selected_product n (a : 'I_n -> B) (b : selection_index n) :=
  word_eval a (selected_indices n b).
(** Source for [selection_coefficient]: Federer (1969), 1.4.5, p. 20,
    divided-power display and following natural isomorphisms. In words: The
    divided m-th power of Gamma(f) is the sum of omega_lambda tensored with
    the m-th exterior image of e_lambda, and equals Gamma of that exterior
    map. Definition or construction used to formalise this passage. *)
Definition selection_coefficient n (a : 'I_n -> B) m :=
  \sum_(b : selection_index n | size (selected_indices n b) == m)
    selected_product a b.
(** Source for [word_eval_map]: Federer (1969), 1.4.5, p. 20, divided-power
    display and following natural isomorphisms. In words: The divided m-th
    power of Gamma(f) is the sum of omega_lambda tensored with the m-th
    exterior image of e_lambda, and equals Gamma of that exterior map.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma word_eval_map (I J : choiceType) (f : I -> J) (a : J -> B) s :
  word_eval a [seq f i | i <- s] = word_eval (fun i => a (f i)) s.
Proof. by elim: s => [|i s ih] //=; rewrite ih. Qed.
(** Source for [selected_product_cons]: Federer (1969), 1.4.5, p. 20,
    divided-power display and following natural isomorphisms. In words: The
    divided m-th power of Gamma(f) is the sum of omega_lambda tensored with
    the m-th exterior image of e_lambda, and equals Gamma of that exterior
    map. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma selected_product_cons n (a : 'I_n.+1 -> B) b t :
  selected_product a (b,t) =
    if b then mul (a ord0) (selected_product (fun i => a (lift ord0 i)) t)
    else selected_product (fun i => a (lift ord0 i)) t.
Proof. by rewrite /selected_product /=; case: b => /=; rewrite word_eval_map. Qed.
(** Source for [selection_coefficient_rec]: Federer (1969), 1.4.5, p. 20,
    divided-power display and following natural isomorphisms. In words: The
    divided m-th power of Gamma(f) is the sum of omega_lambda tensored with
    the m-th exterior image of e_lambda, and equals Gamma of that exterior
    map. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma selection_coefficient_rec n (a : 'I_n.+1 -> B) m :
  selection_coefficient a m =
    (if m is k.+1 then mul (a ord0) (selection_coefficient (fun i => a (lift ord0 i)) k) else 0) +
    selection_coefficient (fun i => a (lift ord0 i)) m.
Proof.
rewrite /selection_coefficient.
have hp : (\sum_(b : selection_index n.+1 | size (selected_indices n.+1 b) == m) selected_product a b) =
    \sum_(b : bool) \sum_(t : selection_index n |
      size (selected_indices n.+1 (b,t)) == m) selected_product a (b,t).
  symmetry; rewrite pair_big_dep; apply: eq_big => [[b t]|[b t] _] //; by [].
rewrite hp big_bool; clear hp.
congr (_ + _).
- case: m => [|m].
  + apply: big_pred0 => t; by rewrite /= size_map.
  + transitivity (\sum_(t : selection_index n | size (selected_indices n t) == m)
      mul (a ord0) (selected_product (fun i => a (lift ord0 i)) t)).
    * apply: eq_big => [t|t _]; first by rewrite /= size_map eqSS.
      exact: selected_product_cons.
    * exact (esym (linear_sum (algebra_left (a ord0)) _ _ _)).
- apply: eq_big => [t|t _]; first by rewrite /= size_map.
  exact: selected_product_cons.
Qed.
(** Source for [selection_coefficient0]: Federer (1969), 1.4.5, p. 20,
    divided-power display and following natural isomorphisms. In words: The
    divided m-th power of Gamma(f) is the sum of omega_lambda tensored with
    the m-th exterior image of e_lambda, and equals Gamma of that exterior
    map. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma selection_coefficient0 n (a : 'I_n -> B) : selection_coefficient a 0 = one.
Proof.
elim: n a => [a|n ih a].
- rewrite /selection_coefficient (big_pred1 tt); last by case.
  by [].
- by rewrite selection_coefficient_rec add0r ih.
Qed.
(** Source for [selection_coefficient_elementary]: Federer (1969), 1.4.5, p.
    20, divided-power display and following natural isomorphisms. In words:
    The divided m-th power of Gamma(f) is the sum of omega_lambda tensored
    with the m-th exterior image of e_lambda, and equals Gamma of that
    exterior map. Supporting lemma for this passage; not separately stated
    in the book. *)
Lemma selection_coefficient_elementary n (a : 'I_n -> B) m :
  selection_coefficient a m = @elementary_symmetric K B [seq a i | i <- enum 'I_n] m.
Proof.
elim: n a m => [a [|m]|n ih a [|m]].
- by rewrite selection_coefficient0 enum_ord0 /=.
- rewrite /selection_coefficient enum_ord0 /=; apply: big_pred0 => [[]]; by [].
- by rewrite selection_coefficient0 enum_ordSl /=.
- by rewrite selection_coefficient_rec enum_ordSl /= -map_comp !ih addrC.
Qed.
(** Source for [selection_coefficient_Lambda]: Federer (1969), 1.4.5, p. 20,
    divided-power display and following natural isomorphisms. In words: The
    divided m-th power of Gamma(f) is the sum of omega_lambda tensored with
    the m-th exterior image of e_lambda, and equals Gamma of that exterior
    map. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma selection_coefficient_Lambda n (a : 'I_n -> B) m :
  selection_coefficient a m =
    \sum_(lambda : Lambda n m) word_eval a (val lambda).
Proof.
rewrite /selection_coefficient sum_subtype.
have hb : bijective (@Lambda_selection n m).
  exists (@selection_Lambda n m); [exact: Lambda_selectionK | exact: selection_LambdaK].
rewrite (reindex (@Lambda_selection n m) (onW_bij _ hb)).
apply: eq_bigr => lambda _; by rewrite /selected_product selection_LambdaE.
Qed.
(** Source for [square_zero_Lambda_power]: Federer (1969), 1.4.5, p. 20,
    divided-power display and following natural isomorphisms. In words: The
    divided m-th power of Gamma(f) is the sum of omega_lambda tensored with
    the m-th exterior image of e_lambda, and equals Gamma of that exterior
    map. Formalises the indicated part of the passage under the hypotheses
    in the statement below. *)
Theorem square_zero_Lambda_power (hc : commutative mul) n (a : 'I_n -> B) :
  (forall i, mul (a i) (a i) = 0) -> forall m,
  @algebra_power K B (\sum_i a i) m = (m`!%:R : K) *:
    \sum_(lambda : Lambda n m) word_eval a (val lambda).
Proof.
move=> ha m.
have hs : forall x, x \in [seq a i | i <- enum 'I_n] -> mul x x = 0.
  move=> x /mapP [i _ ->]; exact: ha.
have h := square_zero_sum_power hc hs m.
rewrite big_map in h.
have hsuma : (\sum_i a i) = (\sum_(i <- enum 'I_n) a i).
  by rewrite product_index_enum.
by rewrite hsuma h -selection_coefficient_elementary selection_coefficient_Lambda.
Qed.
End SelectionPowers.
