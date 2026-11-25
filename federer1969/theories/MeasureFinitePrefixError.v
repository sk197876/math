(** Federer (1969), 2.3.5, p. 76, finite-prefix step Source context:
    SmallBorelPartitionUP.v. The finite-measure hypothesis concerns A, not
    the whole space. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureFiniteClosure
  MeasureSequencePrefixes MeasureContinuityAbove SetSequenceDisjointification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_finite_prefix_error]: supporting decreasing
    continuity step in Federer 2.3.5, p. 76, last display.
    A finite prefix retains any strict bound on the limiting error. *)
Lemma measure_finite_prefix_error (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (E : nat -> set X) (e : \bar R) : measure_measurable mu A ->
  mu A < +oo -> (forall n, measure_measurable mu (E n)) ->
  mu (A `\` \bigcup_n E n) < e ->
  exists N, mu (A `\` set_sequence_prefix E N) < e.
Proof.
move=> hA hf hE he; pose F n := A `\` set_sequence_prefix E n.
have hF n : measure_measurable mu (F n).
  apply: (@measure_measurable_difference R X mu hm _ _ hA).
  exact: (@measure_sequence_prefix_measurable R X mu hm E hE n).
have hmono n m : (n <= m)%N -> F m `<=` F n.
  move=> hnm x [hx hn]; split=> //; move=> hp; apply: hn.
  exact: (@set_sequence_prefix_mono X E n m hnm x hp).
have hfin : mu (F 0%N) < +oo by rewrite /F set_sequence_prefix_zero setD0.
have hlim := @measure_continuity_above R X mu hm F hF hmono hfin.
have heq : (\bigcap_n F n) = A `\` \bigcup_n E n.
  apply/seteqP; split.
  - move=> x hx; split; first exact: (hx 0%N Logic.I).1.
    move=> [n _ hn]; apply: (hx n.+1 Logic.I).2.
    exists n=> //; exact: ltnSn.
  - move=> x [hx hn] n _; split=> //; move=> [k _ hk]; apply: hn; by exists k.
rewrite heq in hlim; have [N hN] := hlim.2.2 e he.
exists N; exact: hN N (leqnn N).
Qed.
