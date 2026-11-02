(** Federer (1969), 1.7.6, p. 33: a map and its adjoint have the same
    operator norm. The proof uses the abstract norm laws, the adjoint
    equation, and the project's Cauchy inequality. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities
  InnerNormalization Bilinear AdjointUP AdjointLaws OperatorNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [inner_normalized_pairing]: Federer 1.7.6,
    p. 33, supporting attainment of the dual pairing bound:
    pairing a vector with its normalisation gives its norm,
    including the zero vector. *)
Lemma inner_normalized_pairing (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) x :
  B x (inner_normalize hB x) = inner_norm hB x.
Proof.
have [->|hx] := eqVneq x 0.
- by rewrite (bil0l (inner_bilinear hB)) inner_norm0.
rewrite /inner_normalize (bilZr (inner_bilinear hB)) -(inner_norm_sqr hB).
change ((inner_norm hB x)^-1 * (inner_norm hB x)^+2 = inner_norm hB x).
by rewrite expr2 mulrA mulVf ?mul1r // inner_norm_eq0.
Qed.

(** Source for [operator_norm_adjoint_le]: Federer 1.7.6,
    p. 33, supporting first half of ||f|| = ||f*||. No choice
    of basis enters this consequence of the abstract norm laws. *)
Lemma operator_norm_adjoint_le (R : rcfType) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    (f : {linear V -> U}) (a : {linear U -> V}) L M :
  is_adjoint B C f a -> is_operator_norm hB hC f L ->
  is_operator_norm hC hB a M -> L <= M.
Proof.
move=> ha hL hM; have [x [hx <-]] := operator_norm_attained hL.
have [hz|hz] := eqVneq (f x) 0.
- rewrite hz inner_norm0; exact: operator_norm_nonnegative hM.
pose y := inner_normalize hC (f x).
have hy : inner_norm hC y <= 1 by rewrite /y inner_normalize_norm.
have hb := @operator_norm_unit_bound R U V C B hC hB a M hM y hy.
have hp : C (f x) y = inner_norm hC (f x) := inner_normalized_pairing hC (f x).
rewrite -hp -ha.
apply: le_trans (ler_norm (B x (a y))) _.
apply: le_trans (inner_cauchy hB x (a y)) _.
apply: le_trans (_ : inner_norm hB x * inner_norm hB (a y) <= inner_norm hB (a y)) hb.
by rewrite -[leRHS]mul1r ler_wpM2r // inner_norm_nonnegative.
Qed.

(** Source for [operator_norm_adjoint_equal]: Federer 1.7.6,
    p. 33, equality of the norms of a linear map and its adjoint. *)
Theorem operator_norm_adjoint_equal (R : rcfType) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    (f : {linear V -> U}) (a : {linear U -> V}) L M :
  is_adjoint B C f a -> is_operator_norm hB hC f L ->
  is_operator_norm hC hB a M -> L = M.
Proof.
move=> ha hL hM; apply/eqP; rewrite eq_le; apply/andP; split.
- exact: operator_norm_adjoint_le ha hL hM.
- exact: operator_norm_adjoint_le (adjoint_reverse hB hC ha) hM hL.
Qed.
