(** Federer (1969), 1.8.1, p. 38: a local boundary correction, not a
    statement of the book or its May 1987 erratum. With the literal
    simple-vector definition of 1.6.1, the only simple zero-vector is the
    empty product 1. Consequently the unsymmetrised supremum in 1.8.1 equals
    the scalar itself in degree zero, and is negative at -1. Source
    editions: SimpleUnitBall.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm ExteriorNorm InnerExteriorLowDegrees
  InnerExterior SimpleZeroDegree ExteriorPowers ExteriorGrading
  AlternatingCoordinates AlternatingPairing Alternating SimpleUnitBall ComassUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Boundary.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.

(** Source for [simple_zero_unit_ball]: Federer 1.8.1,
    p. 38, local boundary analysis of S: in degree zero it is
    the singleton containing the empty product, rather than [-1,1]. *)
Lemma simple_zero_unit_ball (x : exterior_power V 0) :
  simple_unit_ball h2 hB x <-> x = exterior_zeroth_inclusion V 1.
Proof.
split=> [[hs hn]|->]; first exact: (proj1 (simple_zero_iff x) hs).
split; first exact: (proj2 (simple_zero_iff _) erefl).
have hn : exterior_norm h2 hB (exterior_zeroth_inclusion V 1) = 1.
  apply: inner_norm_value; first exact: ler01.
  by rewrite expr1n exterior_inner_zeroth mul1r.
by rewrite hn.
Qed.

(** Source for [literal_zeroth_comass]: Federer 1.8.1,
    p. 38, local correction: the printed supremum at degree zero
    has value c on the constant zero-form c, without absolute value. *)
Theorem literal_zeroth_comass (c : R) :
  is_comass h2 hB (zero_form V (c : R^o)) c.
Proof.
have hp x : simple_unit_ball h2 hB x -> pairing x (zero_form V (c : R^o)) = c.
  move/simple_zero_unit_ball=> ->.
  by rewrite -empty_e_lambda pairing_tuple zero_formE.
constructor.
- move=> x hx; by rewrite (hp x hx).
- move=> eps heps; exists (exterior_zeroth_inclusion V 1).
  have hx := proj2 (simple_zero_unit_ball _) erefl.
  split=> //; rewrite (hp _ hx) ltrBlDr ltrDl; exact heps.
Qed.

(** Source for [literal_zeroth_comass_negative]: Federer 1.8.1,
    p. 38, checked counterexample to a norm assertion in degree zero
    under the literal empty-product convention: the supremum at -1
    is -1 and hence negative. Positive-degree hypotheses avoid this. *)
Theorem literal_zeroth_comass_negative c :
  is_comass h2 hB (zero_form V (-1 : R^o)) c -> c < 0.
Proof.
move=> hc; have -> := comass_unique hc (literal_zeroth_comass (-1)).
exact: ltrN10.
Qed.
End Boundary.
