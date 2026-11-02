(** Federer (1969), 1.7.6, pp. 33-34: the operator norm of an exterior power
    and its estimate. The definition uses the generic sealed norm interface
    and the already proved exterior basis. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP InnerNorm InnerExterior InnerExteriorPositivity
  ExteriorNorm ExteriorMaps ExteriorGrading FiniteExteriorPowers ExteriorIndices
  LinearBasis FiniteOrdinalBasis OperatorNormUP OperatorNorm OperatorNormLaws
  OperatorNormAdjoint AdjointUP ExteriorAdjoint ExteriorOperatorEstimate.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section ExteriorNorm.
Variable R : realType.
Hypothesis h2 : (1+1 : R) != 0.
Variables V U : lmodType R.
Variable B : V -> V -> R.
Variable C : U -> U -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Variable f : {linear V -> U}.
Variable m : nat.
Local Notation hE := (@exterior_inner_productP R h2 V B hB m).
Local Notation hF := (@exterior_inner_productP R h2 U C hC m).

(** Source for [exterior_operator_norm]: Federer 1.7.6,
    p. 33, the norm of the induced exterior map, using its
    finite-dimensional source basis only as an existence witness. *)
Definition exterior_operator_norm := linear_operator_norm hE hF
  (finite_ordinal_basis (@finite_e_lambda_basis R n V b hb h2 m))
  (exterior_power_map f m).

(** Source for [exterior_operator_normP]: Federer 1.7.6,
    p. 33, the exterior operator norm obeys the same unit-ball
    specification as the original map norm. *)
Theorem exterior_operator_normP :
  is_operator_norm hE hF (exterior_power_map f m) exterior_operator_norm.
Proof. exact: linear_operator_normP. Qed.

(** Source for [exterior_operator_norm_bound]: Federer 1.7.6,
    pp. 33-34, ||exterior_m f|| <= ||f||^m, with no positive
    degree or injectivity restriction. *)
Theorem exterior_operator_norm_bound :
  exterior_operator_norm <= (linear_operator_norm hB hC hb f)^+m.
Proof.
apply: (proj2 (operator_norm_le_unit exterior_operator_normP _)) => x hx.
have hh := @exterior_operator_pointwise_bound R h2 V U B C hB hC n b hb f
  (linear_operator_norm hB hC hb f) (linear_operator_normP hB hC hb f) m x.
apply: le_trans hh _.
rewrite -[leRHS]mulr1; apply: ler_wpM2l => //.
exact: exprn_ge0 (linear_operator_norm_nonnegative hB hC hb f).
Qed.
End ExteriorNorm.

(** Source for [exterior_operator_adjoint_norm_equal]: Federer
    1.7.6, p. 33, equality of the operator norms of the
    exterior powers of a map and of its adjoint. *)
Theorem exterior_operator_adjoint_norm_equal (R : realType)
    (h2 : (1+1 : R) != 0) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n k (b : 'I_n -> V) (e : 'I_k -> U) (hb : is_basis b) (he : is_basis e)
    (f : {linear V -> U}) (a : {linear U -> V}) (ha : is_adjoint B C f a) m :
  exterior_operator_norm h2 hB hC hb f m = exterior_operator_norm h2 hC hB he a m.
Proof.
apply: (@operator_norm_adjoint_equal R (exterior_power V m) (exterior_power U m)
  (@exterior_inner_form R h2 V B hB m) (@exterior_inner_form R h2 U C hC m)
  (@exterior_inner_productP R h2 V B hB m) (@exterior_inner_productP R h2 U C hC m)
  (exterior_power_map f m) (exterior_power_map a m)).
- exact (@exterior_power_adjoint R h2 V U B C hB hC f a ha m).
- exact: exterior_operator_normP.
- exact: exterior_operator_normP.
Qed.
