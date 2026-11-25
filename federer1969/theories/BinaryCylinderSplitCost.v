(** Splitting a cylinder across another cylinder preserves its covering
    budget. This proves measurability for the concrete counterexample to
    Federer (1969), 2.3.8, p. 78, using the definition in 2.1.2, p. 54, and
    the fixed-family covering construction of 2.10.1, p. 170. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumRestriction MeasureUP MeasureIndexedCover
  BinarySequenceCylinders BinaryCylinderPrefixLaws BinaryCylinderCost BinaryCylinderRefinementCost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [binary_cylinder_split_cost]: supporting refinement
    argument for the local Federer 2.3.8 counterexample:
    refine both words to a common length, separate the finite
    extension family, and use conservation of its total cost. *)
Lemma binary_cylinder_split_cost (R : realType)
    (mu : set binary_sequence_space -> \bar R) (hm : is_measure mu) :
  (forall w, mu (binary_cylinder w) <= @binary_cylinder_cost R w) ->
  forall w a, mu (binary_cylinder w `&` binary_cylinder a) +
    mu (binary_cylinder w `\` binary_cylinder a) <= @binary_cylinder_cost R w.
Proof.
move=> hb w a; pose n := maxn (size w) (size a).
have hwn : (size w <= n)%N := leq_maxl _ _.
have han : (size a <= n)%N := leq_maxr _ _.
pose I := [the finType of n.-tuple bool].
pose D : set I := [set u | prefix w u].
pose P : set I := [set u | prefix a u].
have hcD : countable (D `&` P) := countableP _.
have hcN : countable (D `\` P) := countableP _.
have hc1 : binary_cylinder w `&` binary_cylinder a `<=`
    \bigcup_(u in D `&` P) binary_cylinder u.
  move=> x [hx ha].
  have [u hu hxu] := @binary_cylinder_finite_refinement n w hwn x hx.
  exists u=> //; split=> //; apply: (@binary_cylinder_meet_prefix a u x _ ha hxu).
  by rewrite size_tuple.
have hc2 : binary_cylinder w `\` binary_cylinder a `<=`
    \bigcup_(u in D `\` P) binary_cylinder u.
  move=> x [hx ha].
  have [u hu hxu] := @binary_cylinder_finite_refinement n w hwn x hx.
  exists u=> //; split=> // hp; apply: ha.
  exact: (@binary_cylinder_prefix_subset a u hp x hxu).
have h1 : mu (binary_cylinder w `&` binary_cylinder a) <=
    nonnegative_sum (D `&` P) (fun u => @binary_cylinder_cost R u).
  apply: le_trans (@measure_indexed_cover R [the choiceType of binary_sequence_space] I mu hm
    _ _ (fun u => binary_cylinder u) hcD hc1) _.
  apply: nonnegative_sum_mono=> u _; exact: hb.
have h2 : mu (binary_cylinder w `\` binary_cylinder a) <=
    nonnegative_sum (D `\` P) (fun u => @binary_cylinder_cost R u).
  apply: le_trans (@measure_indexed_cover R [the choiceType of binary_sequence_space] I mu hm
    _ _ (fun u => binary_cylinder u) hcN hc2) _.
  apply: nonnegative_sum_mono=> u _; exact: hb.
apply: le_trans (leeD h1 h2) _.
rewrite -nonnegative_sum_split; last by move=> u _; exact: ltW (binary_cylinder_cost_positive R u).
by rewrite /D binary_cylinder_refinement_sum.
Qed.
