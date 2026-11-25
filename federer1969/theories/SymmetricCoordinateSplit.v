(** Federer (1969), 1.9.2, p. 42: dimension induction for monomial bases
    uses the splitting K^(n+1)=K+K^n. This file applies the abstract binary
    direct-sum theorem to the coordinate splitting. Arbitrary fields are
    allowed. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Graded UnitalGradedTensor FiniteCoordinates
  SymmetricAlgebra SymmetricGrading SymmetricMaps SymmetricDirectSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CoordinateSplit.
Variable K : fieldType.
Variable n : nat.
Local Notation V := (coordinate_space K n.+1).
Local Notation W := (coordinate_space K n).
Local Notation A := (symmetric_unital K^o).
Local Notation B := (symmetric_unital W).
Local Notation T := (unital_graded_tensor A B false).
Local Notation f := (GRing.Linear.clone _ _ _ _ (@coordinate_head K n) _).
Local Notation g := (GRing.Linear.clone _ _ _ _ (@coordinate_tail K n) _).
Local Notation phi := (GRing.Linear.clone _ _ _ _ (@coordinate_head_inclusion K n) _).
Local Notation psi := (GRing.Linear.clone _ _ _ _ (@coordinate_tail_inclusion K n) _).

(** Source for [symmetric_coordinate_split]: Federer 1.9.2,
    p. 42, the direct-sum isomorphism in the special case K+K^n.
    The forward map separates first and remaining coordinates. *)
Definition symmetric_coordinate_split : algebra_map (symmetric_algebra V) T :=
  symmetric_sum_forward f g.

(** Source for [symmetric_coordinate_join]: Federer 1.9.2,
    p. 42, the inverse direct-sum map multiplies the symmetric
    products after including their factors into K^(n+1). *)
Definition symmetric_coordinate_join : algebra_map T (symmetric_algebra V) :=
  symmetric_sum_backward phi psi.

(** Source for [symmetric_coordinate_splitK]: Federer 1.9.2,
    p. 42, splitting followed by joining is the identity. The
    coordinate splitting satisfies the three abstract direct-sum laws. *)
Lemma symmetric_coordinate_splitK : cancel symmetric_coordinate_split symmetric_coordinate_join.
Proof.
exact (@symmetric_sum_forwardK K V K^o W f phi g psi (@coordinate_decomposition K n)).
Qed.

(** Source for [symmetric_coordinate_joinK]: Federer 1.9.2,
    p. 42, joining followed by splitting is the identity on the
    ordinary tensor product of the two symmetric algebras. *)
Lemma symmetric_coordinate_joinK : cancel symmetric_coordinate_join symmetric_coordinate_split.
Proof.
exact: (@symmetric_sum_backwardK K V K^o W f phi g psi
  (@coordinate_headK K n) (@coordinate_tailK K n) (@coordinate_decomposition K n)).
Qed.

(** Source for [symmetric_coordinate_split_graded]: Federer 1.9.2,
    p. 42, the direct-sum isomorphism preserves the grading. *)
Lemma symmetric_coordinate_split_graded :
  preserves_grading (symmetric_grading V) (unital_grading T) symmetric_coordinate_split.
Proof. exact: symmetric_sum_forward_graded. Qed.

(** Source for [symmetric_coordinate_join_graded]: Federer 1.9.2,
    p. 42, the inverse direct-sum isomorphism preserves the grading. *)
Lemma symmetric_coordinate_join_graded :
  preserves_grading (unital_grading T) (symmetric_grading V) symmetric_coordinate_join.
Proof. exact: symmetric_sum_backward_graded. Qed.

(** Source for [symmetric_coordinate_joinE]: Federer 1.9.2,
    p. 42, the inverse isomorphism takes a pure tensor to the
    product of the two included symmetric elements. *)
Lemma symmetric_coordinate_joinE x y :
  symmetric_coordinate_join (tensor_inj x y) =
    symmetric_product (symmetric_algebra_map phi x) (symmetric_algebra_map psi y).
Proof. exact: symmetric_sum_backwardE. Qed.
End CoordinateSplit.
