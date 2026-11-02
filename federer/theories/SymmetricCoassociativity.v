(** Federer (1969), 1.9.4, p. 43: associativity of the diagonal. The proof
    compares the two unital algebra maps on generating vectors. Arbitrary
    fields and dimensions are allowed. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Graded SymmetricUP SymmetricAlgebra
  SymmetricGrading SymmetricMaps SymmetricDirectSum.
From Federer Require Import UnitalGradedTensor GradedTensorLaws TensorAssociator GradedTensorAssociator SymmetricDiagonal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Coassociativity.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation E := (symmetric_unital V).
Local Notation T := (unital_graded_tensor E E false).
Local Notation L := (unital_graded_tensor T E false).
Local Notation R := (unital_graded_tensor E T false).
Local Notation D := (symmetric_diagonal V).
Local Notation u := (symmetric_unit V).
Local Notation idE := (algebra_id E).

(** Source for [symmetric_diagonal_left]: Federer 1.9.4, p. 43.
    Apply the diagonal to the left tensor factor and the identity to the
    right factor. *)
Definition symmetric_diagonal_left : algebra_map T L := @unital_tensor_map K E E T E D idE
  (@symmetric_diagonal_graded K V) (fun n x hx => hx) false.

(** Source for [symmetric_diagonal_right]: Federer 1.9.4, p. 43.
    Apply the identity to the left tensor factor and the diagonal to the
    right factor. *)
Definition symmetric_diagonal_right : algebra_map T R := @unital_tensor_map K E E E T idE D
  (fun n x hx => hx) (@symmetric_diagonal_graded K V) false.

(** Source for [symmetric_diagonal_leftE]: Federer 1.9.4, p. 43.
    Supporting generator calculation: the left iteration places the
    generator in each of the three positions among units. *)
Lemma symmetric_diagonal_leftE v : symmetric_diagonal_left (D (symmetric_generator v)) =
  tensor_inj (tensor_inj (symmetric_generator v) u) u +
  tensor_inj (tensor_inj u (symmetric_generator v)) u +
  tensor_inj (tensor_inj u u) (symmetric_generator v).
Proof.
pose z := symmetric_generator v.
have hD0 : D u = tensor_inj u u := algebra_map_one D.
have hDz : D z = tensor_inj z u + tensor_inj u z := symmetric_diagonalE v.
have hz : symmetric_diagonal_left (tensor_inj z u) =
    tensor_inj (tensor_inj z u) u + tensor_inj (tensor_inj u z) u.
  apply: eq_trans (@tensor_mapE K E E T E D idE z u) _.
  apply: eq_trans (congr1 (fun x : T => tensor_inj x u) hDz) _.
  exact: tensor_inj_addl.
have hu : symmetric_diagonal_left (tensor_inj u z) = tensor_inj (tensor_inj u u) z.
  apply: eq_trans (@tensor_mapE K E E T E D idE u z) _.
  exact (congr1 (fun x : T => tensor_inj x z) hD0).
apply: eq_trans (congr1 symmetric_diagonal_left hDz) _.
rewrite linearD; exact (congr2 (+%R) hz hu).
Qed.

(** Source for [symmetric_diagonal_rightE]: Federer 1.9.4, p. 43.
    Supporting generator calculation: the right iteration gives the same
    three terms with the other parenthesisation. *)
Lemma symmetric_diagonal_rightE v : symmetric_diagonal_right (D (symmetric_generator v)) =
  tensor_inj (symmetric_generator v) (tensor_inj u u) +
  (tensor_inj u (tensor_inj (symmetric_generator v) u) +
   tensor_inj u (tensor_inj u (symmetric_generator v))).
Proof.
pose z := symmetric_generator v.
have hD0 : D u = tensor_inj u u := algebra_map_one D.
have hDz : D z = tensor_inj z u + tensor_inj u z := symmetric_diagonalE v.
have hz : symmetric_diagonal_right (tensor_inj z u) = tensor_inj z (tensor_inj u u).
  apply: eq_trans (@tensor_mapE K E E E T idE D z u) _.
  exact (congr1 (fun x : T => tensor_inj z x) hD0).
have hu : symmetric_diagonal_right (tensor_inj u z) =
    tensor_inj u (tensor_inj z u) + tensor_inj u (tensor_inj u z).
  apply: eq_trans (@tensor_mapE K E E E T idE D u z) _.
  apply: eq_trans (congr1 (fun x : T => tensor_inj u x) hDz) _.
  exact: tensor_inj_addr.
apply: eq_trans (congr1 symmetric_diagonal_right hDz) _.
rewrite linearD; exact (congr2 (+%R) hz hu).
Qed.

(** Source for [symmetric_diagonal_coassociative]: Federer 1.9.4, p. 43.
    The two iterated diagonals agree after the canonical tensor associator.
    This formalises the final sentence asserting associativity of the
    diagonal. *)
Theorem symmetric_diagonal_coassociative x : tensor_associator E E E (symmetric_diagonal_left (D x)) = symmetric_diagonal_right (D x).
Proof.
have hc : commutative (alg_mul R).
  exact: (@ordinary_tensor_commutative K (unital_graded_view E) (unital_graded_view T)
    (@symmetric_product_commute K V) (@symmetric_tensor_commutative K V V)).
apply: (symmetric_algebra_ext (@symmetric_algebra_exists K V) hc
  (algebra_comp (unital_tensor_associator E E E false) (algebra_comp symmetric_diagonal_left D))
  (algebra_comp symmetric_diagonal_right D)) x => v.
change (tensor_associator E E E (symmetric_diagonal_left (D (symmetric_generator v))) =
  symmetric_diagonal_right (D (symmetric_generator v))).
pose z := symmetric_generator v.
pose a := tensor_inj (tensor_inj z u) u.
pose b := tensor_inj (tensor_inj u z) u.
pose c := tensor_inj (tensor_inj u u) z.
pose f := tensor_associator E E E.
have hd : f (a+b+c) = (f a+f b)+f c by rewrite !linearD.
have h1 := @tensor_associatorE K E E E z u u.
have h2' := @tensor_associatorE K E E E u z u.
have h3 := @tensor_associatorE K E E E u u z.
apply: eq_trans (congr1 f (@symmetric_diagonal_leftE v)) _.
apply: eq_trans hd _.
apply: eq_trans (congr2 (+%R) (congr2 (+%R) h1 h2') h3) _.
apply: eq_trans (esym (addrA _ _ _)) _.
exact: esym (@symmetric_diagonal_rightE v).
Qed.
End Coassociativity.
