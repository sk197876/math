(** Federer (1969), 1.7.6, p. 33: public operator norm and its supremum
    formula. All proofs use the sealed laws. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import boolp classical_sets reals.
From Federer Require Import InnerProductUP InnerNorm LinearBasis
  OperatorNormUP OperatorNormSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Norm.
Variable R : realType.
Variables V U : lmodType R.
Variable B : V -> V -> R.
Variable C : U -> U -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Variable f : {linear V -> U}.

(** Source for [linear_operator_norm]: Federer 1.7.6, p. 33,
    the operator norm, supplied by the sealed existence interface. *)
Definition linear_operator_norm := @OperatorNorm.value R V U B C hB hC n b hb f.

(** Source for [linear_operator_normP]: Federer 1.7.6, p. 33,
    the public norm satisfies the unit-ball bound and attainment laws. *)
Theorem linear_operator_normP : is_operator_norm hB hC f linear_operator_norm.
Proof. exact: OperatorNorm.laws. Qed.

(** Source for [linear_operator_norm_nonnegative]: Federer 1.7.6,
    p. 33, nonnegativity of the norm number. *)
Lemma linear_operator_norm_nonnegative : 0 <= linear_operator_norm.
Proof. exact: operator_norm_nonnegative linear_operator_normP. Qed.

(** Source for [linear_operator_norm_bound]: Federer 1.7.6,
    pp. 33-34, the homogeneous image bound for every vector. *)
Theorem linear_operator_norm_bound x :
  inner_norm hC (f x) <= linear_operator_norm * inner_norm hB x.
Proof. exact: operator_norm_vector_bound linear_operator_normP x. Qed.

(** Source for [linear_operator_unit_values]: Federer 1.7.6,
    p. 33, the set of image lengths on the closed unit ball. *)
Definition linear_operator_unit_values : set R :=
  [set r | exists x, inner_norm hB x <= 1 /\ r = inner_norm hC (f x)].

(** Source for [linear_operator_norm_supremum]: Federer 1.7.6,
    p. 33, the defining printed formula: ||f|| equals the supremum
    of |f(x)| for |x| at most one, including zero-dimensional sources. *)
Theorem linear_operator_norm_supremum :
  linear_operator_norm = sup linear_operator_unit_values.
Proof.
have hu : ubound linear_operator_unit_values linear_operator_norm.
  move=> r [x [hx ->]].
  exact: (@operator_norm_unit_bound R V U B C hB hC f _ linear_operator_normP x hx).
have [x [hx he]] := operator_norm_attained linear_operator_normP.
have hL : linear_operator_unit_values linear_operator_norm.
  exists x; split=> //; exact: esym he.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: ub_le_sup hL; by exists linear_operator_norm.
- apply: ge_sup hu; by exists linear_operator_norm.
Qed.
End Norm.

(** Source for [linear_operator_norm_basis_independent]: Federer
    1.7.6, p. 33, the norm depends only on the inner products and
    the map, not on the basis used to prove its existence. *)
Theorem linear_operator_norm_basis_independent (R : realType)
    (V U : lmodType R) (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n k (b : 'I_n -> V) (c : 'I_k -> V)
    (hb : is_basis b) (hc : is_basis c) (f : {linear V -> U}) :
  linear_operator_norm hB hC hb f = linear_operator_norm hB hC hc f.
Proof. exact: operator_norm_unique (linear_operator_normP _ _ _ _) (linear_operator_normP _ _ _ _). Qed.
