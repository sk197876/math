(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import ExteriorBases.
From Federer Require Import UnitalTensorSymmetry.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.3.3, first paragraph: Psi, the diagonal map of the exterior
    algebra. Its source and target carry the same quotient construction
    and signed tensor product as in 1.3.1 and 1.3.2. *)
Section Diagonal.
Variable K : fieldType.
Hypothesis h2 : (1 + 1 : K) != 0.
Variable V : lmodType K.
Local Notation E := (exterior_unital V).
Local Notation T := (unital_graded_tensor E E true).
(** Source for [Psi]: Federer (1969), 1.3.3, p. 15, opening definition of
    the diagonal map. In words: The diagonal is the unit-preserving algebra
    map into the signed tensor square sending v to v tensor 1 plus 1 tensor
    v. Definition or construction used to formalise this passage. *)
Definition Psi : algebra_map (exterior_algebra V) T := alpha h2 (linear_id V) (linear_id V).
(** Source for [PsiE]: Federer (1969), 1.3.3, p. 15, opening definition of
    the diagonal map. In words: The diagonal is the unit-preserving algebra
    map into the signed tensor square sending v to v tensor 1 plus 1 tensor
    v. Formalises the indicated part of the passage under the hypotheses in
    the statement below. *)
Lemma PsiE v : Psi (exterior_generator v) =
  tensor_inj (exterior_generator v) (exterior_unit V) +
  tensor_inj (exterior_unit V) (exterior_generator v).
Proof. exact: alphaE. Qed.
(** Source for [Psi_graded]: Federer (1969), 1.3.3, p. 15, opening
    definition of the diagonal map. In words: The diagonal is the
    unit-preserving algebra map into the signed tensor square sending v to v
    tensor 1 plus 1 tensor v. Formalises the indicated part of the passage
    under the hypotheses in the statement below. *)
Lemma Psi_graded : preserves_grading (exterior_grading V) (unital_grading T) Psi.
Proof. exact: alpha_graded. Qed.
(** Source for [Psi_unique]: Federer (1969), 1.3.3, p. 15, opening
    definition of the diagonal map. In words: The diagonal is the
    unit-preserving algebra map into the signed tensor square sending v to v
    tensor 1 plus 1 tensor v. Formalises the indicated part of the passage
    under the hypotheses in the statement below. *)
Lemma Psi_unique (h : algebra_map (exterior_algebra V) T) :
  (forall v, h (exterior_generator v) =
    tensor_inj (exterior_generator v) (exterior_unit V) +
      tensor_inj (exterior_unit V) (exterior_generator v)) -> forall x, h x = Psi x.
Proof. exact: (@alpha_unique K h2 V V V (linear_id V) (linear_id V) h). Qed.

(** Federer 1.3.3, product before the shuffle formula. *)
(** Source for [Psi_word]: Federer (1969), 1.3.3, p. 15, opening definition
    of the diagonal map. In words: The diagonal is the unit-preserving
    algebra map into the signed tensor square sending v to v tensor 1 plus 1
    tensor v. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Lemma Psi_word s : Psi (exterior_word s) =
  foldr (alg_mul T) (alg_one T)
    [seq tensor_inj (exterior_generator v) (exterior_unit V) +
      tensor_inj (exterior_unit V) (exterior_generator v) | v <- s].
Proof.
elim: s => [|v s ih].
- exact: (algebra_map_one Psi).
- rewrite exterior_word_cons.
  apply: eq_trans (@algebra_map_mul K (exterior_algebra V) T Psi (exterior_generator v) (exterior_word s)) _.
  by rewrite PsiE ih.
Qed.

(** Federer 1.3.3, anticommutativity of the diagonal map. Federer's alpha
    here is the signed interchange automorphism, not the direct-sum map. *)
(** Source for [Psi_anticommutative]: Federer (1969), 1.3.3, p. 16, opening
    paragraph on anticommutativity of the diagonal. In words: Composing the
    diagonal with signed interchange gives the same diagonal, because the
    maps agree on generating vectors. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem Psi_anticommutative x : unital_tensor_swap E E true (Psi x) = Psi x.
Proof.
apply: (exterior_algebra_ext (@exterior_algebra_exists K V)
  (algebra_comp (unital_tensor_swap E E true) Psi) Psi) x => v.
change (graded_swap (exterior_grading V) (exterior_grading V) true
  (Psi (exterior_generator v)) = Psi (exterior_generator v)).
have hl : graded_swap (exterior_grading V) (exterior_grading V) true
    (tensor_inj (exterior_generator v) (exterior_unit V)) =
    tensor_inj (exterior_unit V) (exterior_generator v).
  apply: eq_trans (@graded_swapE K (exterior_space V) (exterior_space V)
    (exterior_grading V) (exterior_grading V) true 1 0
    (exterior_generator v) (exterior_unit V)
    (exterior_generator_homogeneous v) (exterior_unit_homogeneous V)) _.
  change ((1 : K) *: tensor_inj (exterior_unit V) (exterior_generator v) =
    tensor_inj (exterior_unit V) (exterior_generator v)); exact: scale1r.
have hr : graded_swap (exterior_grading V) (exterior_grading V) true
    (tensor_inj (exterior_unit V) (exterior_generator v)) =
    tensor_inj (exterior_generator v) (exterior_unit V).
  apply: eq_trans (@graded_swapE K (exterior_space V) (exterior_space V)
    (exterior_grading V) (exterior_grading V) true 0 1
    (exterior_unit V) (exterior_generator v)
    (exterior_unit_homogeneous V) (exterior_generator_homogeneous v)) _.
  change ((1 : K) *: tensor_inj (exterior_generator v) (exterior_unit V) =
    tensor_inj (exterior_generator v) (exterior_unit V)); exact: scale1r.
rewrite PsiE linearD.
change (graded_swap (exterior_grading V) (exterior_grading V) true
    (tensor_inj (exterior_generator v) (exterior_unit V)) +
  graded_swap (exterior_grading V) (exterior_grading V) true
    (tensor_inj (exterior_unit V) (exterior_generator v)) =
  tensor_inj (exterior_generator v) (exterior_unit V) +
    tensor_inj (exterior_unit V) (exterior_generator v)).
apply: eq_trans (congr2 (+%R) hl hr) _; exact: addrC.
Qed.
End Diagonal.

(** Federer 1.3.3, last paragraph: the diagonal map is natural. *)
Section Naturality.
Variable K : fieldType.
Hypothesis h2 : (1 + 1 : K) != 0.
Variables V W : lmodType K.
Variable f : {linear V -> W}.
Local Notation EV := (exterior_unital V).
Local Notation EW := (exterior_unital W).
Local Notation F := (exterior_algebra_map f).
Local Notation TF := (@unital_tensor_map K EV EV EW EW F F
  (@exterior_algebra_map_graded K V W f) (@exterior_algebra_map_graded K V W f) true).

(** Source for [Psi_natural]: Federer (1969), 1.3.3, p. 16, naturality
    paragraph and displayed identity. In words: Taking the diagonal commutes
    with applying the exterior map induced by a linear map to both tensor
    factors. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Theorem Psi_natural x : Psi h2 W (F x) = tensor_map F F (Psi h2 V x).
Proof.
apply: (exterior_algebra_ext (@exterior_algebra_exists K V)
  (algebra_comp (Psi h2 W) F) (algebra_comp TF (Psi h2 V))) x => v.
change (Psi h2 W (F (exterior_generator v)) = tensor_map F F (Psi h2 V (exterior_generator v))).
have hfv := @exterior_algebra_mapE K V W f v.
have hf1 : F (exterior_unit V) = exterior_unit W := algebra_map_one F.
have hl : tensor_map F F (tensor_inj (exterior_generator v) (exterior_unit V)) =
    tensor_inj (exterior_generator (f v)) (exterior_unit W).
  apply: eq_trans (@tensor_mapE K (exterior_space V) (exterior_space V)
    (exterior_space W) (exterior_space W) F F (exterior_generator v) (exterior_unit V)) _.
  exact (congr2 (@tensor_inj K (exterior_space W) (exterior_space W)) hfv hf1).
have hr : tensor_map F F (tensor_inj (exterior_unit V) (exterior_generator v)) =
    tensor_inj (exterior_unit W) (exterior_generator (f v)).
  apply: eq_trans (@tensor_mapE K (exterior_space V) (exterior_space V)
    (exterior_space W) (exterior_space W) F F (exterior_unit V) (exterior_generator v)) _.
  exact (congr2 (@tensor_inj K (exterior_space W) (exterior_space W)) hf1 hfv).
apply: eq_trans (congr1 (Psi h2 W) hfv) _.
apply: eq_trans (@PsiE K h2 W (f v)) _; symmetry.
rewrite (@PsiE K h2 V v) linearD.
exact (congr2 (+%R) hl hr).
Qed.
End Naturality.

(** Federer 1.3.3: retain the name alpha for this paragraph's signed
    interchange, qualified to distinguish it from alpha in 1.3.2. *)
Module FedererDiagonal.
Section Interchange.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation E := (exterior_unital V).
(** Source for [alpha]: Federer (1969), 1.3.3, p. 16, opening paragraph on
    anticommutativity of the diagonal. In words: Composing the diagonal with
    signed interchange gives the same diagonal, because the maps agree on
    generating vectors. Definition or construction used to formalise this
    passage. *)
Definition alpha := unital_tensor_swap E E true.
(** Source for [alphaE]: Federer (1969), 1.3.3, p. 16, opening paragraph on
    anticommutativity of the diagonal. In words: Composing the diagonal with
    signed interchange gives the same diagonal, because the maps agree on
    generating vectors. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Lemma alphaE p q x y :
  homogeneous (exterior_grading V) p x ->
  homogeneous (exterior_grading V) q y ->
  alpha (tensor_inj x y) = (-1 : K)^+(p*q) *: tensor_inj y x.
Proof. move=> hx hy; exact: (graded_swapE true hx hy). Qed.
(** Source for [alphaK]: Federer (1969), 1.3.3, p. 16, opening paragraph on
    anticommutativity of the diagonal. In words: Composing the diagonal with
    signed interchange gives the same diagonal, because the maps agree on
    generating vectors. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma alphaK : involutive alpha.
Proof. exact: graded_swapK. Qed.
(** Source for [alpha_Psi]: Federer (1969), 1.3.3, p. 16, opening paragraph
    on anticommutativity of the diagonal. In words: Composing the diagonal
    with signed interchange gives the same diagonal, because the maps agree
    on generating vectors. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma alpha_Psi (h2 : (1 + 1 : K) != 0) x : alpha (Psi h2 V x) = Psi h2 V x.
Proof. exact: Psi_anticommutative. Qed.
End Interchange.
End FedererDiagonal.
