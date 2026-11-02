(** Federer (1969), 2.1.3(5), p. 55: continuity along decreasing measurable
    sets with finite first measure. As in Federer, apply continuity from
    below to the complements relative to the first set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import ExtendedRealOrderLimit ExtendedRealDifferenceLimit
  MeasureUP MeasureBasic MeasureFiniteClosure MeasureCountableClosure
  MeasureContinuityBelow.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_continuity_above]: Federer 2.1.3(5),
    p. 55; measures of decreasing measurable sets converge decreasingly
    to the measure of their intersection. The finite-first-measure
    hypothesis is retained, and natural indices start at zero. *)
Theorem measure_continuity_above (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (F : nat -> set I) :
  (forall n, measure_measurable mu (F n)) ->
  (forall n m, (n <= m)%N -> F m `<=` F n) -> mu (F 0%N) < +oo ->
  extended_decreases_to (fun n => mu (F n)) (mu (\bigcap_n F n)).
Proof.
move=> hF hmono hfin; split.
- move=> n m hnm; exact: (@measure_mono R I mu hm _ _ (hmono n m hnm)).
- pose D n := F 0%N `\` F n.
  have hD : forall n, measure_measurable mu (D n).
    move=> n; exact: (@measure_measurable_difference R I mu hm _ _ (hF 0%N) (hF n)).
  have hDm : forall n m, (n <= m)%N -> D n `<=` D m.
    move=> n m hnm x [hx hn]; split=> //.
    move=> hxM; apply: hn; exact: hmono n m hnm x hxM.
  have hlim := ((@measure_continuity_below R I mu hm D hD hDm)).2.
  have hsub : forall n, F n `<=` F 0%N by move=> n; apply: hmono; exact: leq0n.
  have hDsub : forall n, D n `<=` F 0%N by move=> n x [hx _].
  have hUsub : (\bigcup_n D n) `<=` F 0%N by move=> x [n _ hx]; exact: hDsub n x hx.
  have hUf : mu (\bigcup_n D n) \is a fin_num.
    rewrite ge0_fin_numE; last exact: (@measure_nonnegative R I mu hm).
    exact: le_lt_trans ((@measure_mono R I mu hm _ _ hUsub)) hfin.
  have hDf : forall n, mu (D n) \is a fin_num.
    move=> n; rewrite ge0_fin_numE; last exact: (@measure_nonnegative R I mu hm).
    exact: le_lt_trans ((@measure_mono R I mu hm _ _ (hDsub n))) hfin.
  have hdiff : forall n, mu (F 0%N) - mu (D n) = mu (F n).
    move=> n.
    have hi : F 0%N `&` F n = F n.
      apply/seteqP; split=> [x [_ hx]|x hx] //; split=> //; exact: hsub n x hx.
    by rewrite (hF n (F 0%N)) hi addeK //; exact: hDf.
  have hI : measure_measurable mu (\bigcap_n F n).
    apply: (@measure_measurable_countable_intersection R I _ mu hm setT F (countableP _)).
    by move=> n _; exact: hF.
  have hi : F 0%N `&` (\bigcap_n F n) = \bigcap_n F n.
    apply/seteqP; split=> [x [_ hx]|x hx] //; split=> //; exact: (hx 0%N Logic.I).
  have hd : F 0%N `\` (\bigcap_n F n) = \bigcup_n D n.
    by rewrite setDE setC_bigcap setI_bigcupr.
  have hvalue : mu (F 0%N) - mu (\bigcup_n D n) = mu (\bigcap_n F n).
    by rewrite (hI (F 0%N)) hi hd addeK.
  have hconst : extended_order_limit (fun _ : nat => mu (F 0%N)) (mu (F 0%N)).
    split=> a ha; exists 0%N=> n _; exact ha.
  have hbound : forall n, mu (D n) <= mu (\bigcup_n D n).
    move=> n; apply: (@measure_mono R I mu hm _ _)=> x hx; by exists n.
  have hdom : (mu (F 0%N) < +oo) || (mu (\bigcup_n D n) < +oo) by rewrite hfin.
  have hresult := @extended_nonnegative_difference_limit R
    (fun _ => mu (F 0%N)) (fun n => mu (D n)) (mu (F 0%N)) (mu (\bigcup_n D n))
    (@measure_nonnegative R I mu hm _) (@measure_nonnegative R I mu hm _)
    hdom (fun _ => lexx _) hbound hconst hlim.
  have he : (fun n => mu (F 0%N) - mu (D n)) = (fun n => mu (F n)).
    apply: funext=> n; exact: hdiff.
  by rewrite he hvalue in hresult.
Qed.
