(** Federer (1969), 2.6.4, pp. 118–119: supporting passage from a
    finite-measure countable union to finite unions in the
    characteristic-function density proof. It follows directly from
    2.1.3(5), p. 55, on the decreasing remainders. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureFiniteClosure MeasureCountableClosure
  MeasureContinuityAbove MeasureSequencePrefixes SetSequenceDisjointification ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_union_measure_approximation]: supporting
    finite-prefix approximation for the P1,P2 density steps of
    Federer 2.6.4, pp. 118–119. Only the measure of
    the union must be finite; the ambient measure is arbitrary. *)
Theorem finite_union_measure_approximation (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : nat -> set X) (e : R) :
  (forall n, measure_measurable mu (A n)) ->
  mu (\bigcup_n A n) < +oo -> (0 < e)%R ->
  exists n, mu ((\bigcup_k A k) `\` set_sequence_prefix A n) < e%:E.
Proof.
move=> hA hfin he; pose W := \bigcup_n A n.
have hW : measure_measurable mu W.
  exact (@measure_measurable_countable_union R X [the choiceType of (nat : Type)] mu hm setT A
    (countableP setT) (fun n _ => hA n)).
pose D n := W `\` set_sequence_prefix A n.
have hD n : measure_measurable mu (D n).
  exact (@measure_measurable_difference R X mu hm _ _ hW
    (@measure_sequence_prefix_measurable R X mu hm A hA n)).
have hmD n m : (n<=m)%N -> D m `<=` D n.
  move=> hnm x [hx hn]; split=> // hp; apply: hn.
  exact (@set_sequence_prefix_mono X A n m hnm x hp).
have h0 : mu (D 0%N) < +oo.
  apply: le_lt_trans (@measure_mono R X mu hm _ W _) hfin.
  by move=> x [hx _].
have hI : (\bigcap_n D n)=set0.
  apply/seteqP; split; last by move=> x [].
  move=> x hx; have [n _ hn] := (hx 0%N I).1.
  have hnot := (hx n.+1 I).2.
  apply: hnot; exists n=> //; exact: ltnSn.
have hh := (@measure_continuity_above R X mu hm D hD hmD h0).2.2.
rewrite hI (measure_empty hm) in hh.
have heE : 0<e%:E by rewrite lte_fin.
have [n hn] := hh e%:E heE; exists n; exact: hn n (leqnn n).
Qed.
