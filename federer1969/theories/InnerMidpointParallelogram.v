(** Federer (1969), 1.7.13, p. 37: the equality in the displayed midpoint
    estimate. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm InnerParallelogram.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [inner_midpoint_sum]: Federer 1.7.13,
    p. 37, supporting vector identity relating twice the
    displacement of the midpoint to the sum of displacements. *)
Lemma inner_midpoint_sum (R : realFieldType) (V : lmodType R) (a x y : V) :
  (2 : R) *: (a - (2 : R)^-1 *: (x+y)) = (a-x)+(a-y).
Proof.
have h2 : (2 : R) != 0 by rewrite pnatr_eq0.
by rewrite scalerBr scalerA mulfV // scale1r scaler_nat mulr2n opprD addrACA.
Qed.

(** Source for [inner_midpoint_parallelogram]: Federer 1.7.13,
    p. 37, equality in the diameter display, multiplied by
    four: four times the squared midpoint distance plus the
    squared chord length equals twice the sum of endpoint
    squared distances. *)
Lemma inner_midpoint_parallelogram (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (a x y : V) :
  4 * inner_norm hB (a-(2 : R)^-1 *: (x+y))^+2 +
    inner_norm hB (x-y)^+2 =
  2 * (inner_norm hB (a-x)^+2 + inner_norm hB (a-y)^+2).
Proof.
have he : (a-x)-(a-y) = -(x-y).
  by rewrite !opprB [y-a]addrC addrACA subrr add0r addrC.
have hp := inner_parallelogram hB (a-x) (a-y).
rewrite -inner_midpoint_sum he inner_normN inner_normZ normr_nat exprMn
  expr2 -natrM in hp.
exact hp.
Qed.
