(** Federer (1969), 1.7.9, p. 35: the two printed norm inequalities,
    instantiated with the public operator norm. The real scalar hypothesis
    comes from existence of the attained operator norm; the abstract
    comparison proofs themselves work over a real-closed field. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP HomInner HomNormBound
  HomNormDimensionBound OperatorNorm LinearBasis Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [hom_operator_norm_comparison]: Federer 1.7.9,
    p. 35, both inequalities for the actual operator and Hom norms:
    ||f|| <= |f| <= sqrt(dim V) ||f||, including dim V = 0. *)
Theorem hom_operator_norm_comparison (R : realType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (e : 'I_n -> V) (he : is_basis e) (f : Hom V W) :
  linear_operator_norm hB hC he (hom_as_linear f) <= hom_norm hB hC he f /\
  hom_norm hB hC he f <= Num.sqrt n%:R * linear_operator_norm hB hC he (hom_as_linear f).
Proof.
split.
- exact (@operator_norm_le_hom_norm R V W B C hB hC n e he f _
    (linear_operator_normP hB hC he (hom_as_linear f))).
- exact (@hom_norm_le_dimension_operator_norm R V W B C hB hC n e he f _
    (linear_operator_normP hB hC he (hom_as_linear f))).
Qed.
