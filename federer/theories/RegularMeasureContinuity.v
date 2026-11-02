(** Federer (1969), 2.1.5(1), pp. 56-57: continuity from below for arbitrary
    sets under regularity. The proof follows the book's measurable supersets
    and tail intersections. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import ExtendedRealOrderLimit ExtendedRealLimitBounds
  MeasureUP MeasureBasic MeasureCountableClosure MeasureContinuityBelow
  RegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [regular_measure_continuity_below]: Federer 2.1.5(1), pp.
    56-57; under regularity the increasing sets need not be measurable. *)
Theorem regular_measure_continuity_below (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (hr : is_regular_measure mu)
    (A : nat -> set I) :
  (forall n m, (n <= m)%N -> A n `<=` A m) ->
  extended_increases_to (fun n => mu (A n)) (mu (\bigcup_n A n)).
Proof.
move=> ha.
pose C n := projT1 (cid (hr (A n))).
have hC n : A n `<=` C n /\ measure_measurable mu (C n) /\ mu (A n) = mu (C n).
  exact: projT2 (cid (hr (A n))).
pose B n := \bigcap_(j in [set j | (n <= j)%N]) C j.
have hB n : measure_measurable mu (B n).
  apply: (@measure_measurable_countable_intersection R I _ mu hm _ C (countableP _)).
  move=> j _; exact: (hC j).2.1.
have hAB n : A n `<=` B n.
  move=> x hx j hj; apply: (hC j).1; exact: ha n j hj x hx.
have hBC n : B n `<=` C n by move=> x hx; exact: (hx n (leqnn n)).
have hval n : mu (B n) = mu (A n).
  apply/eqP; rewrite eq_le; apply/andP; split.
  - rewrite (hC n).2.2; exact: (@measure_mono R I mu hm _ _ (hBC n)).
  - exact: (@measure_mono R I mu hm _ _ (hAB n)).
have hBm : forall n m, (n <= m)%N -> B n `<=` B m.
  move=> n m hnm x hx j hj; apply: hx; exact: leq_trans hnm hj.
have hlim := @measure_continuity_below R I mu hm B hB hBm.
have hsub : (\bigcup_n A n) `<=` \bigcup_n B n.
  move=> x [n _ hx]; exists n=> //; exact: hAB n x hx.
have hv : mu (\bigcup_n B n) = mu (\bigcup_n A n).
  apply/eqP; rewrite eq_le; apply/andP; split.
  - apply: extended_order_limit_upper_bound hlim.2 _=> n.
    rewrite hval; apply: (@measure_mono R I mu hm _ _)=> x hx; by exists n.
  - exact: (@measure_mono R I mu hm _ _ hsub).
have he : (fun n => mu (B n)) = (fun n => mu (A n)) by apply: funext=> n; exact: hval.
by rewrite he hv in hlim.
Qed.
