(** Federer (1969), 2.3.8, p. 79, final argument: finite measure of the
    nonzero locus makes sufficiently high norm tails small. Source context:
    MeasureGauge.v. The proof follows decreasing continuity from 2.1.3(5),
    retaining its essential finite-initial-measure hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP MeasureUP MeasureBasic
  MeasureContinuityAbove MeasureGauge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_norm_integer_tails_empty]: supporting
    empty-intersection assertion for Federer 2.3.8, p. 79:
    every defined function value has a finite real norm. *)
Lemma partial_norm_integer_tails_empty (R : realType) (X Y : Type)
    (N : Y -> R) (f : partial_function X Y) :
  (forall y, (0 <= N y)%R) ->
  (\bigcap_n partial_norm_superlevel N f (n%:R : R)%:E) = set0.
Proof.
move=> hN; apply/seteqP; split; last by move=> x [].
move=> x hx; have [y [hy _]] := hx 0%N Logic.I.
pose n := Num.bound (N y).
have hn : (N y < n%:R)%R by apply: archi_boundP; exact: hN.
have [z [hz hb]] := hx n Logic.I.
have he := partial_function_single_valued hy hz.
have hb' : (n%:R < N z)%R := hb.
by move: hb'; rewrite -he ltNge (ltW hn).
Qed.

(** Source for [measure_norm_tail_small]: direct tail choice in Federer
    2.3.8, p. 79, final paragraph Measurable superlevels and finite measure
    of the positive-norm locus suffice. *)
Theorem measure_norm_tail_small (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (hm : is_measure mu) (N : Y -> R)
    (f : partial_function X Y) (e : R) :
  (forall y, (0 <= N y)%R) ->
  (forall t : R, measure_measurable mu (partial_norm_superlevel N f t%:E)) ->
  mu (partial_norm_superlevel N f 0) < +oo -> (0 < e)%R ->
  exists n, mu (partial_norm_superlevel N f (n.+1%:R : R)%:E) < e%:E.
Proof.
move=> hN hme hfin he.
pose F n := partial_norm_superlevel N f (n%:R : R)%:E.
have hmono n m (hnm : (n <= m)%N) : F m `<=` F n.
  apply: partial_norm_superlevel_antitone; by rewrite lee_fin ler_nat.
have hc := @measure_continuity_above R X mu hm F (fun n => hme _) hmono hfin.
have hz : mu (\bigcap_n F n) = 0.
  rewrite (@partial_norm_integer_tails_empty R X Y N f hN); exact: measure_empty.
have hp : mu (\bigcap_n F n) < e%:E by rewrite hz lte_fin.
have [n hn] := hc.2.2 e%:E hp.
exists n; exact: hn n.+1 (leqnSn n).
Qed.
