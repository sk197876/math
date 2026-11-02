(** Federer (1969), 1.8.1, p. 38, first supremum definition. Upper bounds
    and arbitrary positive-error approximation specify the supremum
    independently of its construction or attainment. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP ExteriorGrading AlternatingCoordinates
  AlternatingPairing ExteriorNorm SimpleUnitBall.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Specification.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable m : nat.

(** Source for [is_comass]: Federer 1.8.1, p. 38, first
    displayed supremum: the least upper bound of evaluations on S.
    No nonnegativity or attainment is built into the specification;
    nonnegativity follows in positive degree from zero membership. *)
Record is_comass (phi : A_m V R^o m) (c : R) : Prop := {
  comass_upper_law : forall x, simple_unit_ball h2 hB x -> pairing x phi <= c;
  comass_approx_law : forall eps, 0 < eps ->
    exists x, simple_unit_ball h2 hB x /\ c-eps < pairing x phi
}.

(** Source for [comass_least_upper_bound]: Federer 1.8.1,
    p. 38, supporting least-upper-bound property of the first display. *)
Lemma comass_least_upper_bound phi c (hc : is_comass phi c) b :
  (forall x, simple_unit_ball h2 hB x -> pairing x phi <= b) -> c <= b.
Proof.
move=> hb; case: (leP c b) => // hbc.
have he : 0 < c-b by rewrite subr_gt0.
have [x [hx hh]] := comass_approx_law hc he.
rewrite opprB addrCA subrr addr0 in hh.
have h := lt_le_trans hh (hb x hx).
by rewrite ltxx in h.
Qed.

(** Source for [comass_unique]: Federer 1.8.1, p. 38,
    supporting uniqueness of the number specified by the supremum. *)
Theorem comass_unique phi c d : is_comass phi c -> is_comass phi d -> c=d.
Proof.
move=> hc hd; apply/eqP; rewrite eq_le; apply/andP; split.
- exact: (comass_least_upper_bound hc (comass_upper_law hd)).
- exact: (comass_least_upper_bound hd (comass_upper_law hc)).
Qed.

(** Source for [comass_nonnegative]: Federer 1.8.1, p. 38, supporting
    nonnegativity of the comass. the literal degree-zero formula is
    excluded. *)
Lemma comass_nonnegative phi c : (0 < m)%N -> is_comass phi c -> 0 <= c.
Proof.
move=> hm hc.
have h := comass_upper_law hc (simple_unit_ball_zero h2 hB hm).
by rewrite (bil0l (@pairing_bilinear R V R^o m)) in h.
Qed.
End Specification.
