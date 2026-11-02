(** Federer (1969), 2.9.19, p. 165: cover a restricted segment by the
    restrictions to two adjacent segments. This is a supporting
    outer-measure covering step and needs no measurability of the restricted
    set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_restricted_segment_split_le]: supporting finite-cell
    covering inequality in Federer 2.9.19, p. 165 The restrictions of [a,b]
    and [b,c] cover the restriction of [a,c]. The splitting point can be
    arbitrary: the real order ensures each point lies on at least one side.
    Only the measure covering law is used. *)
Lemma real_restricted_segment_split_le (R : realType) (mu : set R -> \bar R)
    (C : set R) (a b c : R) : is_measure mu ->
  mu (C `&` `[a,c])<=mu (C `&` `[a,b])+mu (C `&` `[b,c]).
Proof.
move=> hm; apply: (@measure_binary_cover R R mu hm).
move=> x [hx hxI]; move: hxI; rewrite /= in_itv /= => /andP [hax hxc].
case: (leP x b)=> hxb.
- left; split=> //; by rewrite /= in_itv /= hax hxb.
- right; split=> //; by rewrite /= in_itv /= (ltW hxb) hxc.
Qed.
