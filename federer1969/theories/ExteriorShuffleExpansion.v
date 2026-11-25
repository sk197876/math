(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import ExteriorBases.
From Federer Require Import ExteriorDiagonal Shuffles.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section SelectedVectors.
Variable K : fieldType.
Variable V : lmodType K.
(** Source for [selected_vectors]: Federer (1969), 1.3.3, p. 15, definition
    of Sh(p,q), shuffle expansion, and definition of index. In words: A
    (p,q)-shuffle is increasing in each consecutive block; the diagonal of a
    product is the sum over all shuffles of the two selected products,
    weighted by permutation index. Definition or construction used to
    formalise this passage. *)
Definition selected_vectors (s : seq V) (b : selection_index (size s)) : seq V :=
  [seq nth 0 s i | i <- map val (selected_indices (size s) b)].
Arguments selected_vectors s b : clear implicits.
(** Source for [selected_vectors_size]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma selected_vectors_size s b : size (selected_vectors s b) = size (selected_indices (size s) b).
Proof. by rewrite /selected_vectors !size_map. Qed.
(** Source for [selected_vectors_cons]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma selected_vectors_cons v s (b : bool) (t : selection_index (size s)) :
  selected_vectors (v :: s) (b,t) = if b then v :: selected_vectors s t else selected_vectors s t.
Proof.
by rewrite /selected_vectors selected_values; case: b => /=; rewrite -!map_comp.
Qed.
(** Source for [selected_word_homogeneous]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma selected_word_homogeneous s b : homogeneous (exterior_grading V)
  (size (selected_indices (size s) b)) (exterior_word (selected_vectors s b)).
Proof. have h := exterior_word_homogeneous (selected_vectors s b); by rewrite selected_vectors_size in h. Qed.
End SelectedVectors.
Arguments selected_vectors {K V} s b.
Arguments selected_word_homogeneous {K V} s b.

(** Federer 1.3.3, rules used to expand the product. The two actions
    correspond exactly to choosing v tensor 1 or 1 tensor v. *)
Section Expansion.
Variable K : fieldType.
Hypothesis h2 : (1 + 1 : K) != 0.
Variable V : lmodType K.
Local Notation E := (exterior_unital V).
Local Notation EG := (unital_graded_view E).
Local Notation T := (unital_graded_tensor E E true).
Local Notation mu := (alg_mul T).
Local Notation D := (Psi h2 V).
Local Notation u := (exterior_unit V).

(** Source for [Psi_left_action]: Federer (1969), 1.3.3, p. 15, definition
    of Sh(p,q), shuffle expansion, and definition of index. In words: A
    (p,q)-shuffle is increasing in each consecutive block; the diagonal of a
    product is the sum over all shuffles of the two selected products,
    weighted by permutation index. Definition or construction used to
    formalise this passage. *)
Definition Psi_left_action v (x : T) := mu (tensor_inj (exterior_generator v) u) x.
(** Source for [Psi_left_action_linear]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma Psi_left_action_linear v : linear (Psi_left_action v).
Proof. exact: (proj2 (alg_bilinear T) _). Qed.
HB.instance Definition _ v := GRing.isLinear.Build K T T *:%R
  (Psi_left_action v) (Psi_left_action_linear v).
(** Source for [Psi_right_action]: Federer (1969), 1.3.3, p. 15, definition
    of Sh(p,q), shuffle expansion, and definition of index. In words: A
    (p,q)-shuffle is increasing in each consecutive block; the diagonal of a
    product is the sum over all shuffles of the two selected products,
    weighted by permutation index. Definition or construction used to
    formalise this passage. *)
Definition Psi_right_action v (x : T) := mu (tensor_inj u (exterior_generator v)) x.
(** Source for [Psi_right_action_linear]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma Psi_right_action_linear v : linear (Psi_right_action v).
Proof. exact: (proj2 (alg_bilinear T) _). Qed.
HB.instance Definition _ v := GRing.isLinear.Build K T T *:%R
  (Psi_right_action v) (Psi_right_action_linear v).

(** Source for [Psi_left_factor]: Federer (1969), 1.3.3, p. 15, definition
    of Sh(p,q), shuffle expansion, and definition of index. In words: A
    (p,q)-shuffle is increasing in each consecutive block; the diagonal of a
    product is the sum over all shuffles of the two selected products,
    weighted by permutation index. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma Psi_left_factor v p a b : homogeneous (exterior_grading V) p a ->
  Psi_left_action v (tensor_inj a b) = tensor_inj (wedge (exterior_generator v) a) b.
Proof.
move=> ha; apply: eq_trans (@graded_tensor_mulE K EG EG true 0 p
  (exterior_generator v) u a b (exterior_unit_homogeneous V) ha) _.
change (koszul K true 0 p *: tensor_inj (wedge (exterior_generator v) a) (wedge u b) =
  tensor_inj (wedge (exterior_generator v) a) b).
by rewrite koszul0l scale1r wedge_unitl.
Qed.
(** Source for [Psi_right_factor]: Federer (1969), 1.3.3, p. 15, definition
    of Sh(p,q), shuffle expansion, and definition of index. In words: A
    (p,q)-shuffle is increasing in each consecutive block; the diagonal of a
    product is the sum over all shuffles of the two selected products,
    weighted by permutation index. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma Psi_right_factor v p a b : homogeneous (exterior_grading V) p a ->
  Psi_right_action v (tensor_inj a b) = (-1 : K)^+p *: tensor_inj a (wedge (exterior_generator v) b).
Proof.
move=> ha; apply: eq_trans (@graded_tensor_mulE K EG EG true 1 p
  u (exterior_generator v) a b (exterior_generator_homogeneous v) ha) _.
change (koszul K true 1 p *: tensor_inj (wedge u a) (wedge (exterior_generator v) b) =
  (-1 : K)^+p *: tensor_inj a (wedge (exterior_generator v) b)).
by rewrite /koszul mul1n wedge_unitl.
Qed.
(** Source for [diagonal_left_right]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Formalises the indicated part
    of the passage under the hypotheses in the statement below. *)
Lemma diagonal_left_right v w :
  mu (tensor_inj (exterior_generator v) u) (tensor_inj u (exterior_generator w)) =
  tensor_inj (exterior_generator v) (exterior_generator w).
Proof.
have h := Psi_left_factor v (exterior_generator w) (exterior_unit_homogeneous V).
by rewrite wedge_unitr in h.
Qed.
(** Source for [diagonal_right_left]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Formalises the indicated part
    of the passage under the hypotheses in the statement below. *)
Lemma diagonal_right_left v w :
  mu (tensor_inj u (exterior_generator w)) (tensor_inj (exterior_generator v) u) =
  - tensor_inj (exterior_generator v) (exterior_generator w).
Proof.
have h := Psi_right_factor w u (exterior_generator_homogeneous v).
by rewrite expr1 scaleN1r wedge_unitr in h.
Qed.
(** Source for [diagonal_crossing]: Federer (1969), 1.3.3, p. 15, definition
    of Sh(p,q), shuffle expansion, and definition of index. In words: A
    (p,q)-shuffle is increasing in each consecutive block; the diagonal of a
    product is the sum over all shuffles of the two selected products,
    weighted by permutation index. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma diagonal_crossing v w :
  mu (tensor_inj (exterior_generator v) u) (tensor_inj u (exterior_generator w)) =
  - mu (tensor_inj u (exterior_generator w)) (tensor_inj (exterior_generator v) u).
Proof.
apply: eq_trans (@diagonal_left_right v w) _.
apply: eq_trans (esym (opprK (tensor_inj (exterior_generator v) (exterior_generator w)))) _.
exact (congr1 (-%R) (esym (@diagonal_right_left v w))).
Qed.

(** Source for [Psi_word_cons]: Federer (1969), 1.3.3, p. 15, definition of
    Sh(p,q), shuffle expansion, and definition of index. In words: A
    (p,q)-shuffle is increasing in each consecutive block; the diagonal of a
    product is the sum over all shuffles of the two selected products,
    weighted by permutation index. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma Psi_word_cons v s : D (exterior_word (v :: s)) =
  Psi_left_action v (D (exterior_word s)) + Psi_right_action v (D (exterior_word s)).
Proof.
rewrite exterior_word_cons.
apply: eq_trans (@algebra_map_mul K (exterior_algebra V) T D (exterior_generator v) (exterior_word s)) _.
apply: eq_trans (congr1 (fun x : T => mu x (D (exterior_word s))) (@PsiE K h2 V v)) _.
exact (bilDl (alg_bilinear T) (tensor_inj (exterior_generator v) u)
  (tensor_inj u (exterior_generator v)) (D (exterior_word s))).
Qed.

(** Source for [selection_term]: Federer (1969), 1.3.3, p. 15, definition of
    Sh(p,q), shuffle expansion, and definition of index. In words: A
    (p,q)-shuffle is increasing in each consecutive block; the diagonal of a
    product is the sum over all shuffles of the two selected products,
    weighted by permutation index. Definition or construction used to
    formalise this passage. *)
Definition selection_term (s : seq V) (b : selection_index (size s)) : T :=
  (-1 : K)^+(@selection_inversions (size s) b) *:
    tensor_inj (exterior_word (selected_vectors s b))
      (exterior_word (selected_vectors s (selection_flip (size s) b))).
Arguments selection_term s b : clear implicits.

(** Source for [selection_term_true]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma selection_term_true v s (t : selection_index (size s)) :
  selection_term (v :: s) (true,t) = Psi_left_action v (selection_term s t).
Proof.
rewrite /selection_term selection_inversions_cons /= !selected_vectors_cons /= exterior_word_cons linearZ.
exact (congr1 ( *:%R ((-1 : K)^+(@selection_inversions (size s) t)))
  (esym (Psi_left_factor v
    (exterior_word (selected_vectors s (selection_flip (size s) t)))
    (selected_word_homogeneous s t)))).
Qed.
(** Source for [selection_term_false]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma selection_term_false v s (t : selection_index (size s)) :
  selection_term (v :: s) (false,t) = Psi_right_action v (selection_term s t).
Proof.
rewrite /selection_term selection_inversions_cons /= !selected_vectors_cons /= exterior_word_cons linearZ.
have hr := Psi_right_factor v
  (exterior_word (selected_vectors s (selection_flip (size s) t)))
  (selected_word_homogeneous s t).
apply: eq_trans _ (esym (congr1 ( *:%R ((-1 : K)^+(@selection_inversions (size s) t))) hr)).
rewrite scalerA exprD; congr (_ *: _); exact: mulrC.
Qed.

(** Federer 1.3.3: distributivity enumerates each choice once. Reindexing
    this sum by the proved shuffle bijection gives Federer's double sum. *)
(** Source for [Psi_selection_formula]: Federer (1969), 1.3.3, p. 15,
    definition of Sh(p,q), shuffle expansion, and definition of index. In
    words: A (p,q)-shuffle is increasing in each consecutive block; the
    diagonal of a product is the sum over all shuffles of the two selected
    products, weighted by permutation index. Formalises the indicated part
    of the passage under the hypotheses in the statement below. *)
Theorem Psi_selection_formula s :
  D (exterior_word s) = \sum_(b : selection_index (size s)) selection_term s b.
Proof.
elim: s => [|v s ih].
- rewrite (big_pred1 tt); last by case.
  change (D u = (1 : K) *: tensor_inj u u).
  rewrite scale1r; exact: (algebra_map_one D).
- have hs : (\sum_(b : selection_index (size (v :: s))) selection_term (v :: s) b) =
      \sum_(b : bool) \sum_(t : selection_index (size s)) selection_term (v :: s) (b,t).
    symmetry; rewrite pair_bigA; apply: eq_bigr => [[b t]] _; by [].
  rewrite Psi_word_cons ih !linear_sum hs big_bool.
  congr (_ + _); apply: eq_bigr => t _.
  + exact (esym (@selection_term_true v s t)).
  + exact (esym (@selection_term_false v s t)).
Qed.
End Expansion.
