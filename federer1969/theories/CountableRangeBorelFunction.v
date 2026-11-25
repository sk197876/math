(** Federer (1969), proof of 2.4.4(2), p. 83: supporting criterion for
    measurability of a countable-valued geometric step approximant. A
    function with countable range and Borel fibres is Borel, by countable
    unions. Source context: MeasureIntegralSqueeze.v. *)
From mathcomp Require Import all_boot classical_sets cardinality topology.
From Federer Require Import BorelFunctionUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [countable_range_borel_function]: supporting
    countable-fibre argument for the geometric approximant in
    Federer 2.4.4(2), p. 83; this is general topology
    infrastructure, not an additional numbered assertion in the book. *)
Lemma countable_range_borel_function (X Y : topologicalType) (f : X -> Y) :
  countable (f @` setT) -> (forall y, borel_set (f @^-1` [set y])) -> is_borel_function f.
Proof.
move=> hc hf U ho.
have he : f @^-1` U = \bigcup_(y in (f @` setT) `&` U) (f @^-1` [set y]).
  apply/seteqP; split=> x hx.
  - exists (f x); last by [].
    split=> //; by exists x.
  - move: hx=> [y [_ hy] he]; change (U (f x)); by rewrite he.
rewrite he; apply: borel_set_countable_union; last by move=> y _; exact: hf.
apply: sub_countable _ hc; apply: subset_card_le=> y [hy _]; exact hy.
Qed.
