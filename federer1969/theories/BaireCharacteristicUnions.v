(** Federer (1969), 2.2.15, p. 71: countable-union closure for the family of
    Baire characteristic functions. Characteristic functions of increasing
    finite prefixes converge pointwise to that of the entire union. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals topology.
From Federer Require Import RealMetricBackground CharacteristicFunctionUP CharacteristicFunctionSealed
  BaireFunctions BaireCharacteristicBasic PointwiseEventuallyConstant
  SetSequenceDisjointification CountableFamilySequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [baire_characteristic_sequence_union]: supporting
    sequential union step for F in Federer 2.2.15,
    p. 71. Once a point enters a finite prefix,
    all later characteristic values equal one; outside the union
    every value is zero. *)
Theorem baire_characteristic_sequence_union (R : realType) (X : topologicalType)
    (A : nat -> set X) :
  (forall n, has_baire_characteristic R (A n)) ->
  has_baire_characteristic R (\bigcup_n A n).
Proof.
move=> hA.
pose P n := set_sequence_prefix A n.
have hP n : has_baire_characteristic R (P n).
  elim: n=> [|n ih].
  - rewrite /P set_sequence_prefix_zero; exact: baire_characteristic_empty.
  - rewrite /P set_sequence_prefix_succ; exact: baire_characteristic_binary_union ih (hA n).
pose f n := @CharacteristicFunction.value R X (P n).
pose g := @CharacteristicFunction.value R X (\bigcup_n A n).
have hf n : is_characteristic_function (P n) (f n) := @CharacteristicFunction.laws R X (P n).
have hg : is_characteristic_function (\bigcup_n A n) g := @CharacteristicFunction.laws R X (\bigcup_n A n).
exists g; split=> //.
apply: (@baire_function_pointwise_limit R X [the metricType R of real_line_metric R] f g).
- move=> n; exact: baire_characteristic_transfer (hP n) (hf n).
- apply: pointwise_eventually_equal_limit=> x.
  case: (pselect ((\bigcup_n A n) x))=> hx.
  + have [i _ hi] := hx; exists i.+1=> n hn.
    have hpx : P n x.
      exists i; last exact hi.
      exact: leq_trans (leqnn i.+1) hn.
    by rewrite (characteristic_on_set (hf n) hpx) (characteristic_on_set hg hx).
  + exists 0%N=> n _.
    have hpx : ~ P n x by move=> [i hi hix]; apply: hx; by exists i.
    by rewrite (characteristic_off_set (hf n) hpx) (characteristic_off_set hg hx).
Qed.

(** Source for [baire_characteristic_countable_union]: literal
    countable-family union closure of F in Federer 2.2.15,
    p. 71. An enumeration may insert empty gaps; their
    characteristic functions are already known to be Baire. *)
Theorem baire_characteristic_countable_union (R : realType) (X : topologicalType)
    (G : set (set X)) : countable G ->
  (forall A, G A -> has_baire_characteristic R A) ->
  has_baire_characteristic R (\bigcup_(A in G) A).
Proof.
move=> hc hG; have [A [hA he]] := @countable_family_as_sequence X
  [the choiceType of set X] G id hc.
rewrite -he; apply: baire_characteristic_sequence_union=> n.
case: (hA n)=> [->|[B [hb ->]]]; first exact: baire_characteristic_empty.
exact: hG B hb.
Qed.
