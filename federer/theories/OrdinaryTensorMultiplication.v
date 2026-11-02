(** Federer (1969), 1.2.2, p. 12, used in 1.9.2, p. 42: multiplication as a
    unital graded homomorphism from the ordinary tensor product of a
    commutative algebra with itself. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Graded UnitalGradedTensor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Multiplication.
Variable K : fieldType.
Variable A : unital_graded_algebra K.
Hypothesis hc : commutative (alg_mul A).

(** Source for [ordinary_Phi]: Federer 1.2.2, p. 12,
    final multiplication-map paragraph, supporting 1.9.2, p. 42.
    In words: Multiplication factors through a unit-preserving algebra homomorphism from the ordinary tensor product. *)
Definition ordinary_Phi : algebra_map (unital_tensor_algebra A A false) A.
Proof.
apply: (@AlgebraMap K (unital_tensor_algebra A A false) A
  (graded_multiplication (unital_graded_view A))).
  change (graded_multiplication (unital_graded_view A)
    (tensor_inj (alg_one A) (alg_one A)) = alg_one A).
  rewrite graded_multiplicationE.
  change (alg_mul A (alg_one A) (alg_one A) = alg_one A).
  exact: alg_unitl.
exact: (@ordinary_multiplication_hom K (unital_graded_view A) (@alg_assoc K A) hc).
Defined.

(** Source for [ordinary_PhiE]: Federer 1.2.2, p. 12,
    final multiplication-map paragraph, supporting 1.9.2, p. 42.
    In words: The induced homomorphism sends a pure tensor to the product of its two factors. *)
Lemma ordinary_PhiE a b : ordinary_Phi (tensor_inj a b) = alg_mul A a b.
Proof. exact: (@graded_multiplicationE K (unital_graded_view A) a b). Qed.

(** Source for [ordinary_Phi_graded]: Federer 1.2.2, p. 12,
    final multiplication-map paragraph, supporting 1.9.2, p. 42.
    In words: The induced multiplication homomorphism preserves homogeneous degree. *)
Lemma ordinary_Phi_graded : preserves_grading
  (unital_grading (unital_graded_tensor A A false)) (unital_grading A) ordinary_Phi.
Proof. exact: (@graded_multiplication_graded K (unital_graded_view A)). Qed.
End Multiplication.
