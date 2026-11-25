(** Federer (1969), 3.1.4, p. 215: one radius index works
    for finitely many increasing good-set families. This groups the
    coordinate conditions before the summable-loss selection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  MeasureCountableClosure FiniteMeasureExhaustionCutoff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_increasing_intersection_union]: the finite
    common-index choice underlying p_j and q_j in Federer 3.1.4,
    p. 215. Increasing families commute with finite intersections,
    including the empty family. *)
Lemma finite_increasing_intersection_union (X : Type) (J : finType)
    (B : J -> nat -> set X) :
  (forall j p q, (p<=q)%N -> B j p `<=` B j q) ->
  (\bigcup_p \bigcap_j B j p)=\bigcap_j \bigcup_p B j p.
Proof.
move=> hm; apply/seteqP; split=> x.
- move=> [p _ hp] j _; exists p=> //; exact: hp j Logic.I.
- move=> hx.
  have he j : exists p, forall q, (p<=q)%N -> B j q x.
    have [p _ hp] := hx j Logic.I; exists p=> q hpq; exact: hm j p q hpq x hp.
  have [p hp] := finite_common_eventual_cutoff he.
  exists p=> // j _; exact: hp j p (leqnn p).
Qed.

(** Source for [finite_conull_increasing_exhaustion]: finite
    simultaneous exhaustion used to select the common p_j and q_j
    in Federer 3.1.4, p. 215. The base set E is arbitrary. *)
Theorem finite_conull_increasing_exhaustion (R : realType) (X : choiceType)
    (J : finType) (mu : set X -> \bar R) (E : set X) (B : J -> nat -> set X) :
  is_measure mu ->
  (forall j p q, (p<=q)%N -> B j p `<=` B j q) ->
  (forall j, mu (E `\` \bigcup_p B j p)=0%E) ->
  mu (E `\` \bigcup_p \bigcap_j B j p)=0%E.
Proof.
move=> hm hmono hnull.
rewrite finite_increasing_intersection_union //.
have hj j : measure_almost_everywhere mu [set x | E x -> (\bigcup_p B j p) x].
  exact: (measure_almost_everywhere_on_implication _ _ _).1 (hnull j).
have hall := @measure_almost_everywhere_countable R X [the choiceType of (J : Type)]
  mu hm setT (fun j=>[set x | E x -> (\bigcup_p B j p) x])
  (@countableP [the countType of (J : Type)] setT) (fun j _=>hj j).
apply: (measure_almost_everywhere_on_implication _ _ _).2.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hall)=> x hx he j _.
exact: hx j Logic.I he.
Qed.
