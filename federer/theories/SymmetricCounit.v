(** Federer (1969), 1.9.4, p. 43: supporting counit identities for the
    diagonal, also used in the unit assertion of 1.10.2, p. 44. The scalar
    counit gives the stated contractions; the identities follow by comparing
    algebra maps on generators. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Graded UnitalGradedTensor Hom TensorPowers OrdinaryTensorMultiplication
  SymmetricUP SymmetricAlgebra SymmetricGrading SymmetricMaps SymmetricDirectSum SymmetricDiagonal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Counit.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation E := (symmetric_unital V).
Local Notation T := (unital_graded_tensor E E false).

(** Source for [symmetric_vector_zero]: Federer 1.9.4, p. 43, supporting
    counit identity Supporting zero linear map on the generating vector
    space. *)
Definition symmetric_vector_zero : {linear V -> V} := hom_as_linear (0 : Hom V V).

(** Source for [symmetric_zero_map]: Federer 1.9.4, p. 43, supporting counit
    identity The unital algebra map induced by the zero map on vectors. *)
Definition symmetric_zero_map := symmetric_algebra_map symmetric_vector_zero.

(** Source for [symmetric_zero_mapE]: Federer 1.9.4, p. 43, supporting
    counit identity The zero-induced map is scalar inclusion after
    augmentation: it keeps degree zero and annihilates every positive
    degree. *)
Lemma symmetric_zero_mapE x : symmetric_zero_map x = symmetric_scalar V (symmetric_augmentation V x).
Proof.
elim/symmetric_word_induction: x => [|x y hx hy|c x hx|s].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
- rewrite /symmetric_zero_map symmetric_algebra_map_word symmetric_augmentation_word.
  case: s => [|v s].
  + by rewrite /word_degree_zero /symmetric_scalar /= scale1r.
  + rewrite map_cons symmetric_word_cons.
    change (symmetric_product (symmetric_generator (0 : V)) (symmetric_word [seq symmetric_vector_zero v | v <- s]) =
      (0 : K) *: symmetric_unit V).
    by rewrite linear0 (bil0l (symmetric_product_bilinear V)) scale0r.
Qed.
Local Notation F := (symmetric_algebra_map symmetric_vector_zero).
Local Notation hf := (@symmetric_algebra_map_graded K V V symmetric_vector_zero).
Local Notation idE := (algebra_id E).
Local Notation P := (@ordinary_Phi K E (@symmetric_product_commute K V)).

(** Source for [symmetric_counit_left]: Federer 1.9.4, p. 43, supporting
    counit identity Contract the left tensor factor by augmentation,
    retaining the right factor. *)
Definition symmetric_counit_left : algebra_map T E :=
  algebra_comp P (@unital_tensor_map K E E E E F idE hf (fun n x hx => hx) false).

(** Source for [symmetric_counit_right]: Federer 1.9.4, p. 43, supporting
    counit identity Contract the right tensor factor by augmentation,
    retaining the left factor. *)
Definition symmetric_counit_right : algebra_map T E :=
  algebra_comp P (@unital_tensor_map K E E E E idE F (fun n x hx => hx) hf false).

(** Source for [symmetric_counit_leftE]: Federer 1.9.4, p. 43, supporting
    counit identity On a pure tensor a tensor b, left contraction gives
    augmentation(a) times b. *)
Lemma symmetric_counit_leftE a b : symmetric_counit_left (tensor_inj a b) = (symmetric_augmentation V a : K) *: b.
Proof.
change (P (tensor_map F idE (tensor_inj a b)) = (symmetric_augmentation V a : K) *: b).
rewrite tensor_mapE ordinary_PhiE.
change (symmetric_product (symmetric_zero_map a) b = (symmetric_augmentation V a : K) *: b).
by rewrite symmetric_zero_mapE /symmetric_scalar (bilZl (symmetric_product_bilinear V)) symmetric_product_unitl.
Qed.

(** Source for [symmetric_counit_rightE]: Federer 1.9.4, p. 43, supporting
    counit identity On a pure tensor a tensor b, right contraction gives
    augmentation(b) times a. *)
Lemma symmetric_counit_rightE a b : symmetric_counit_right (tensor_inj a b) = (symmetric_augmentation V b : K) *: a.
Proof.
change (P (tensor_map idE F (tensor_inj a b)) = (symmetric_augmentation V b : K) *: a).
rewrite tensor_mapE ordinary_PhiE.
change (symmetric_product a (symmetric_zero_map b) = (symmetric_augmentation V b : K) *: a).
by rewrite symmetric_zero_mapE /symmetric_scalar (bilZr (symmetric_product_bilinear V)) symmetric_product_unitr.
Qed.

(** Source for [symmetric_counit_left_symmetric_diagonal]: Federer 1.9.4, p.
    43, supporting counit identity Applying augmentation to the left factor
    after the diagonal recovers the original element. *)
Lemma symmetric_counit_left_symmetric_diagonal x : symmetric_counit_left (symmetric_diagonal V x) = x.
Proof.
apply: (symmetric_algebra_ext (@symmetric_algebra_exists K V) (@symmetric_product_commute K V)
  (algebra_comp symmetric_counit_left (symmetric_diagonal V)) idE) x => v.
change (symmetric_counit_left (symmetric_diagonal V (symmetric_generator v)) = symmetric_generator v).
have h0 : symmetric_augmentation V (symmetric_generator v) = 0 := symmetric_augmentation_word [::v].
have hl := @symmetric_counit_leftE (symmetric_generator v) (symmetric_unit V).
rewrite h0 scale0r in hl.
have hr := @symmetric_counit_leftE (symmetric_unit V) (symmetric_generator v).
rewrite symmetric_augmentation_unit scale1r in hr.
apply: eq_trans (congr1 symmetric_counit_left (@symmetric_diagonalE K V v)) _.
apply: eq_trans (linD (linearP symmetric_counit_left) _ _) _.
exact (eq_trans (congr2 +%R hl hr) (add0r _)).
Qed.

(** Source for [symmetric_counit_right_symmetric_diagonal]: Federer 1.9.4,
    p. 43, supporting counit identity Applying augmentation to the right
    factor after the diagonal recovers the original element. *)
Lemma symmetric_counit_right_symmetric_diagonal x : symmetric_counit_right (symmetric_diagonal V x) = x.
Proof.
apply: (symmetric_algebra_ext (@symmetric_algebra_exists K V) (@symmetric_product_commute K V)
  (algebra_comp symmetric_counit_right (symmetric_diagonal V)) idE) x => v.
change (symmetric_counit_right (symmetric_diagonal V (symmetric_generator v)) = symmetric_generator v).
have h0 : symmetric_augmentation V (symmetric_generator v) = 0 := symmetric_augmentation_word [::v].
have hl := @symmetric_counit_rightE (symmetric_generator v) (symmetric_unit V).
rewrite symmetric_augmentation_unit scale1r in hl.
have hr := @symmetric_counit_rightE (symmetric_unit V) (symmetric_generator v).
rewrite h0 scale0r in hr.
apply: eq_trans (congr1 symmetric_counit_right (@symmetric_diagonalE K V v)) _.
apply: eq_trans (linD (linearP symmetric_counit_right) _ _) _.
exact (eq_trans (congr2 +%R hl hr) (addr0 _)).
Qed.
End Counit.
