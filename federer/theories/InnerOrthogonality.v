(** Federer (1969), 1.7.1, p. 28: supporting orthogonality facts for the
    compactness criterion. Source context are recorded in InnerProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities
  OrthonormalFamilies FiniteSpans Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Orthogonality.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.

(** Source for [inner_orthogonal_span]: Federer 1.7.1, p. 28,
    supporting fact: orthogonality to generators implies orthogonality
    to their linear span. *)
Lemma inner_orthogonal_span n (e : 'I_n -> V) w z :
  (forall i, B w (e i) = 0) -> in_finite_span e z -> B w z = 0.
Proof.
move=> hw [c ->]; rewrite (inner_symmetric hB) -(inner_coordinateE hB) linear_sum.
apply: big1 => i _; rewrite linearZ inner_coordinateE (inner_symmetric hB) hw.
change (c i * 0 = 0); exact: mulr0.
Qed.

(** Source for [inner_unit_orthogonal_distance]: Federer 1.7.1,
    p. 28, supporting separation fact: a unit vector orthogonal to z
    is at distance at least one from z. Used to rule out a finite
    small-ball cover of the unit ball in infinite dimension. *)
Lemma inner_unit_orthogonal_distance w z :
  inner_norm hB w = 1 -> B w z = 0 -> 1 <= inner_norm hB (w-z).
Proof.
move=> hw hz.
have hs : B w (w-z) = 1.
  rewrite (inner_symmetric hB) -(inner_coordinateE hB) linearB !inner_coordinateE.
  rewrite (inner_symmetric hB z w) hz subr0 -(inner_norm_sqr hB w) hw expr1n.
  by [].
have hc := @inner_cauchy_upper R V B hB w (w-z).
by rewrite hs hw mul1r in hc.
Qed.
End Orthogonality.
