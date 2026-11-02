(** Federer (1969), 2.5.7, p. 99: finite-measure covering sets for the
    weighted scalar functional in the p=1 case. The proof below adjoins one
    positive finite-mass set to every member of a finite-mass cover,
    preserving coverage of null pieces while making every reciprocal valid. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit MeasureFiniteClosure MeasureAlmostBasic
  CountablyMeasurableUP CountablyMeasurableSequences.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_finite_measurable_cover]: supporting choice of 0 <
    phi(A_n) < infinity in Federer 2.5.7, p. 99 The zero-measure case is
    excluded here and treated separately. *)
Theorem positive_finite_measurable_cover (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  measure_countably_measurable mu setT -> 0 < mu setT ->
  exists F : nat -> set X, setT=\bigcup_n F n /\
    forall n, measure_measurable mu (F n) /\ 0 < mu (F n) < +oo.
Proof.
move=> hX hpos.
have [F [hcover hF]] := (proj1 (@countably_measurable_sequence_iff R X mu hm setT)) hX.
have hex : exists n, 0 < mu (F n).
  apply: contrapT=> hnone.
  have hz n : mu (F n)=0.
    apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT leNgt.
    apply/negP=> hp; apply: hnone; by exists n.
  have hnat : countable (setT : set nat) by exact: countableP.
  have hu := @measure_null_countable_union R X [the choiceType of (nat : Type)] mu hm setT F
    hnat (fun n _ => hz n).
  rewrite -hcover in hu; by rewrite hu ltxx in hpos.
have [m hmpos] := hex.
exists (fun n => F n `|` F m); split.
- apply/seteqP; split=> x _; last by [].
  have hx : (\bigcup_n F n) x by rewrite -hcover.
  have [n _ hn] := hx; exists n=> //; by left.
- move=> n; split.
  + exact: (@measure_measurable_union R X mu hm (F n) (F m) (hF n).1 (hF m).1).
  + apply/andP; split.
    * apply: lt_le_trans hmpos _; apply: (@measure_mono R X mu hm)=> x hx; by right.
    * have hnf : mu (F n) \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hm _)); exact: (hF n).2.
      have hmf : mu (F m) \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hm _)); exact: (hF m).2.
      have hb := @measure_binary_cover R X mu hm (F n `|` F m) (F n) (F m) (fun x hx => hx).
      apply: le_lt_trans hb _; rewrite -(fineK hnf) -(fineK hmf) -EFinD; exact: ltry.
Qed.
