(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From mathcomp.classical Require Import boolp.
From Federer Require Import AlternatingCoordinates.
From Federer Require Import DisjointBlocks.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.4, infinite-dimensional assertion *)
Section Blocks.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Local Notation N := (Choice.clone nat _).
Local Notation F := (GRing.Lmodule.clone K (free_vector K N) _).
Local Notation d := (@delta K N).
Variable m : nat.
(** Source for [block_value]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Definition or construction used
    to formalise this passage. *)
Definition block_value (lambda : Lambda_infty m) : K^o :=
  if `[< exists j, lambda = block_lambda m j >] then 1 else 0.
Local Notation hb := (@countable_e_lambda_basis K h2 F d (free_basis K N) m).
(** Source for [block_functional]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Definition or construction used
    to formalise this passage. *)
Definition block_functional : Hom (exterior_power F m) K^o := hom_of_linear
  (linear_comp (GRing.Linear.clone _ _ _ _ (free_extend block_value) _) (basis_coordinates hb)).
(** Source for [block_covector]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Definition or construction used
    to formalise this passage. *)
Definition block_covector : A_m F K^o m := hom_to_form block_functional.
(** Source for [block_covector_basis]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma block_covector_basis (lambda : Lambda_infty m) :
  form_include block_covector (exterior_word [seq d i | i <- val lambda]) = block_value lambda.
Proof.
change (pairing (e_lambda d (val lambda)) block_covector = block_value lambda).
rewrite /pairing /block_covector hom_to_formK /block_functional hom_of_linearE.
change (free_extend block_value (basis_coordinates hb (countable_e_lambda d lambda)) = block_value lambda).
by rewrite basis_coordinatesE free_extend_delta.
Qed.
(** Source for [block_value_block]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma block_value_block j : block_value (block_lambda m j) = 1.
Proof.
have hh : `[< exists k, block_lambda m j = block_lambda m k >] by apply/asboolP; exists j.
by rewrite /block_value hh.
Qed.
(** Source for [block_covector_block]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma block_covector_block j :
  form_include block_covector (exterior_word [seq d i | i <- block_tuple m j]) = 1.
Proof. exact (eq_trans (block_covector_basis (block_lambda m j)) (block_value_block j)). Qed.
(** Source for [block_covector_other]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Theorem block_covector_other s : size s = m ->
  (forall j, ~~ perm_eq s (block_tuple m j)) ->
  form_include block_covector (exterior_word [seq d i | i <- s]) = 0.
Proof.
move=> hs hn; case hu : (uniq s).
- have hsz : size (order_indices s) == m by apply/eqP; rewrite (perm_size (order_indices_perm s)).
  pose t : m.-tuple nat := Tuple hsz.
  have ht : sorted ltn t.
    change (sorted ltn (order_indices s)); rewrite ltn_sorted_uniq_leq order_indices_sorted andbT.
    by rewrite (perm_uniq (order_indices_perm s)) hu.
  pose lambda : Lambda_infty m := Sub t ht.
  have hz : block_value lambda = 0.
    rewrite /block_value; case hb' : `[< exists j, lambda = block_lambda m j >] => //.
    move/asboolP: hb' => [j hj].
    have hseq := congr1 (fun z : Lambda_infty m => val (val z)) hj.
    change (order_indices s = block_tuple m j) in hseq.
    have hp : perm_eq s (block_tuple m j) by rewrite -hseq perm_sym; exact: order_indices_perm.
    exfalso; exact (elimT negP (hn j) hp).
  have hv : form_include block_covector (exterior_word [seq d i | i <- order_indices s]) = 0.
    exact (eq_trans (block_covector_basis lambda) hz).
  rewrite (exterior_word_order d s) (linZ (hom_linear (form_include block_covector))) hv scaler0.
  by [].
- by rewrite (exterior_word_map_nonuniq d (negbT hu)) linear0.
Qed.
End Blocks.

(** Source for [block_covector_mixed]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Theorem block_covector_mixed (K : fieldType) (h2 : (1+1 : K) != 0) m i j :
  form_include (@block_covector K h2 m.+2)
    (exterior_word [seq delta K k | k <- mixed_block m i j]) =
    if i == j then 1 else 0.
Proof.
case hij : (i == j).
- move/eqP: hij => ->; rewrite mixed_block_diagonal; exact: block_covector_block.
- apply: block_covector_other; first exact: mixed_block_size.
  exact: mixed_block_not_permutation (negbT hij).
Qed.
