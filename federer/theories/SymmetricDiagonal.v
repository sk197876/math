(** Federer (1969), 1.9.4, p. 43: the diagonal of the symmetric algebra, its
    generator values, commutativity and naturality. Arbitrary fields are
    allowed. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Graded SymmetricUP SymmetricAlgebra
  SymmetricGrading SymmetricMaps SymmetricDirectSum.
From Federer Require Import UnitalGradedTensor UnitalTensorSymmetry.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Diagonal.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation E := (symmetric_unital V).
Local Notation T := (unital_graded_tensor E E false).

(** Source for [symmetric_diagonal]: Federer 1.9.4, p. 43.
    The unique unital graded algebra map taking v to v tensor 1 plus 1 tensor v, using the ordinary tensor product. *)
Definition symmetric_diagonal : algebra_map (symmetric_algebra V) T := symmetric_sum_forward (linear_id V) (linear_id V).

(** Source for [symmetric_diagonalE]: Federer 1.9.4, p. 43.
    The diagonal has the prescribed two-term value on every generating vector. *)
Lemma symmetric_diagonalE v : symmetric_diagonal (symmetric_generator v) =
  tensor_inj (symmetric_generator v) (symmetric_unit V) +
  tensor_inj (symmetric_unit V) (symmetric_generator v).
Proof. exact: symmetric_sum_forwardE. Qed.

(** Source for [symmetric_diagonal_graded]: Federer 1.9.4, p. 43.
    The diagonal preserves total degree in the tensor product. *)
Lemma symmetric_diagonal_graded : preserves_grading (symmetric_grading V) (unital_grading T) symmetric_diagonal.
Proof. exact: symmetric_sum_forward_graded. Qed.

(** Source for [symmetric_diagonal_unique]: Federer 1.9.4, p. 43.
    Any unital algebra map with these generator values equals the diagonal. *)
Lemma symmetric_diagonal_unique (h : algebra_map (symmetric_algebra V) T) :
  (forall v, h (symmetric_generator v) =
    tensor_inj (symmetric_generator v) (symmetric_unit V) +
      tensor_inj (symmetric_unit V) (symmetric_generator v)) -> forall x, h x = symmetric_diagonal x.
Proof. exact: (@symmetric_sum_forward_unique K V V V (linear_id V) (linear_id V) h). Qed.

(** Source for [symmetric_diagonal_word]: Federer 1.9.4, p. 43.
    The diagonal of a product is the product of the two-term diagonals of its factors, including the empty product. *)
Lemma symmetric_diagonal_word s : symmetric_diagonal (symmetric_word s) =
  foldr (alg_mul T) (alg_one T)
    [seq tensor_inj (symmetric_generator v) (symmetric_unit V) +
      tensor_inj (symmetric_unit V) (symmetric_generator v) | v <- s].
Proof.
elim: s => [|v s ih].
- exact: (algebra_map_one symmetric_diagonal).
- rewrite symmetric_word_cons.
  apply: eq_trans (@algebra_map_mul K (symmetric_algebra V) T symmetric_diagonal (symmetric_generator v) (symmetric_word s)) _.
  by rewrite symmetric_diagonalE ih.
Qed.

(** Source for [symmetric_diagonal_commutative]: Federer 1.9.4, p. 43.
    Ordinary interchange of the two tensor factors leaves the diagonal unchanged. This is the commutativity assertion in the final sentence. *)
Theorem symmetric_diagonal_commutative x : unital_tensor_swap E E false (symmetric_diagonal x) = symmetric_diagonal x.
Proof.
apply: (symmetric_algebra_ext (@symmetric_algebra_exists K V)
  (@symmetric_tensor_commutative K V V)
  (algebra_comp (unital_tensor_swap E E false) symmetric_diagonal) symmetric_diagonal) x => v.
change (graded_swap (symmetric_grading V) (symmetric_grading V) false
  (symmetric_diagonal (symmetric_generator v)) = symmetric_diagonal (symmetric_generator v)).
have hl : graded_swap (symmetric_grading V) (symmetric_grading V) false
    (tensor_inj (symmetric_generator v) (symmetric_unit V)) =
    tensor_inj (symmetric_unit V) (symmetric_generator v).
  apply: eq_trans (@graded_swapE K (symmetric_space V) (symmetric_space V)
    (symmetric_grading V) (symmetric_grading V) false 1 0
    (symmetric_generator v) (symmetric_unit V)
    (symmetric_generator_homogeneous v) (symmetric_unit_homogeneous V)) _.
  change ((1 : K) *: tensor_inj (symmetric_unit V) (symmetric_generator v) =
    tensor_inj (symmetric_unit V) (symmetric_generator v)); exact: scale1r.
have hr : graded_swap (symmetric_grading V) (symmetric_grading V) false
    (tensor_inj (symmetric_unit V) (symmetric_generator v)) =
    tensor_inj (symmetric_generator v) (symmetric_unit V).
  apply: eq_trans (@graded_swapE K (symmetric_space V) (symmetric_space V)
    (symmetric_grading V) (symmetric_grading V) false 0 1
    (symmetric_unit V) (symmetric_generator v)
    (symmetric_unit_homogeneous V) (symmetric_generator_homogeneous v)) _.
  change ((1 : K) *: tensor_inj (symmetric_generator v) (symmetric_unit V) =
    tensor_inj (symmetric_generator v) (symmetric_unit V)); exact: scale1r.
rewrite symmetric_diagonalE linearD.
change (graded_swap (symmetric_grading V) (symmetric_grading V) false
    (tensor_inj (symmetric_generator v) (symmetric_unit V)) +
  graded_swap (symmetric_grading V) (symmetric_grading V) false
    (tensor_inj (symmetric_unit V) (symmetric_generator v)) =
  tensor_inj (symmetric_generator v) (symmetric_unit V) +
    tensor_inj (symmetric_unit V) (symmetric_generator v)).
apply: eq_trans (congr2 (+%R) hl hr) _; exact: addrC.
Qed.
End Diagonal.

Section Naturality.
Variable K : fieldType.
Variables V W : lmodType K.
Variable f : {linear V -> W}.
Local Notation EV := (symmetric_unital V).
Local Notation EW := (symmetric_unital W).
Local Notation F := (symmetric_algebra_map f).
Local Notation TF := (@unital_tensor_map K EV EV EW EW F F
  (@symmetric_algebra_map_graded K V W f) (@symmetric_algebra_map_graded K V W f) false).

(** Source for [symmetric_diagonal_natural]: Federer 1.9.4, p. 43.
    The diagonal commutes with the algebra maps induced by an arbitrary linear map, applied to both tensor factors. This is the naturality assertion in the final sentence. *)
Theorem symmetric_diagonal_natural x : symmetric_diagonal W (F x) = tensor_map F F (symmetric_diagonal V x).
Proof.
apply: (symmetric_algebra_ext (@symmetric_algebra_exists K V)
  (@symmetric_tensor_commutative K W W)
  (algebra_comp (symmetric_diagonal W) F) (algebra_comp TF (symmetric_diagonal V))) x => v.
change (symmetric_diagonal W (F (symmetric_generator v)) = tensor_map F F (symmetric_diagonal V (symmetric_generator v))).
have hfv := @symmetric_algebra_mapE K V W f v.
have hf1 : F (symmetric_unit V) = symmetric_unit W := algebra_map_one F.
have hl : tensor_map F F (tensor_inj (symmetric_generator v) (symmetric_unit V)) =
    tensor_inj (symmetric_generator (f v)) (symmetric_unit W).
  apply: eq_trans (@tensor_mapE K (symmetric_space V) (symmetric_space V)
    (symmetric_space W) (symmetric_space W) F F (symmetric_generator v) (symmetric_unit V)) _.
  exact (congr2 (@tensor_inj K (symmetric_space W) (symmetric_space W)) hfv hf1).
have hr : tensor_map F F (tensor_inj (symmetric_unit V) (symmetric_generator v)) =
    tensor_inj (symmetric_unit W) (symmetric_generator (f v)).
  apply: eq_trans (@tensor_mapE K (symmetric_space V) (symmetric_space V)
    (symmetric_space W) (symmetric_space W) F F (symmetric_unit V) (symmetric_generator v)) _.
  exact (congr2 (@tensor_inj K (symmetric_space W) (symmetric_space W)) hf1 hfv).
apply: eq_trans (congr1 (symmetric_diagonal W) hfv) _.
apply: eq_trans (@symmetric_diagonalE K W (f v)) _; symmetry.
rewrite (@symmetric_diagonalE K V v) linearD.
exact (congr2 (+%R) hl hr).
Qed.
End Naturality.
