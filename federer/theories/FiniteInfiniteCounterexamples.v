(** Federer (1969), 2.1.5, p. 57, first irregular example: failures of
    increasing continuity and finite hull existence. Here the natural
    numbers start at zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import ExtendedRealOrderLimit MeasureUP MeasureHull
  RegularMeasureUP FiniteInfiniteMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_infinite_singleton_no_hull]: Federer 2.1.5, p. 57,
    failure of (2) The singleton at zero has measure one but no hull. *)
Theorem finite_infinite_singleton_no_hull (R : realType) :
  forall B, ~ is_measure_hull (@finite_infinite_measure R _) [set 0%N] B.
Proof.
move=> B h.
have h0 : [set 0%N] != (@set0 nat).
  apply/eqP=> he; have hx : [set 0%N] 0%N by []; by rewrite he in hx.
have hv := @measure_hull_equal_measure R _ _ (@finite_infinite_measure_is_measure R _) _ _ h.
rewrite (@finite_infinite_measure_finite R _ [set 0%N] h0 (finite_set1 _)) in hv.
have hm := measure_hull_measurable h.
have [he|he] := proj1 (@finite_infinite_measure_measurable_iff R _ B infinite_nat) hm.
- rewrite he finite_infinite_measure_empty in hv.
  have h01 : (0 : \bar R) < 1 by rewrite lte_fin ltr01.
  by rewrite hv ltxx in h01.
- rewrite he (@finite_infinite_measure_infinite R _ setT infinite_nat) in hv.
  have h12 : (1 : \bar R) < (2 : R)%:E by rewrite lte_fin ltr1n.
  by rewrite -hv ltxx in h12.
Qed.

(** Source for [finite_infinite_continuity_counterexample]: Federer 2.1.5,
    p. 57, failure of (1); increasing finite initial segments have value
    one, whereas their union has value two. Monotonicity and nonconvergence
    are explicit. *)
Theorem finite_infinite_continuity_counterexample (R : realType) :
  exists A : nat -> set nat,
    (forall n m, (n <= m)%N -> A n `<=` A m) /\
    (forall n, finite_infinite_measure (R := R) (A n) = (1 : R)%:E) /\
    finite_infinite_measure (R := R) (\bigcup_n A n) = (2 : R)%:E /\
    ~ extended_order_limit (fun n => finite_infinite_measure (R := R) (A n))
        (finite_infinite_measure (R := R) (\bigcup_n A n)).
Proof.
pose A n := [set k | (k < n.+1)%N].
have hm : forall n m, (n <= m)%N -> A n `<=` A m.
  move=> n m hnm k hk; apply: leq_trans hk _; by rewrite ltnS.
have hv n : finite_infinite_measure (R := R) (A n) = (1 : R)%:E.
  apply: finite_infinite_measure_finite; last exact: finite_II.
  apply/eqP=> he; have hx : A n 0%N by rewrite /A /= ltn0Sn.
  by rewrite he in hx.
have hu : (\bigcup_n A n) = setT.
  apply/seteqP; split=> [k _|k _] //; exists k=> //; exact: ltnSn.
have hU : finite_infinite_measure (R := R) (\bigcup_n A n) = (2 : R)%:E.
  by rewrite hu (@finite_infinite_measure_infinite R _ setT infinite_nat).
exists A; split=> //; split=> //; split=> //.
rewrite hU; move=> [hl _].
have h12 : (1 : \bar R) < (2 : R)%:E by rewrite lte_fin ltr1n.
have [N hN] := hl 1 h12; have h := hN N (leqnn N).
by rewrite hv ltxx in h.
Qed.

(** Source for [finite_infinite_measure_not_regular]: Federer 2.1.5, p. 57,
    first example is irregular, as witnessed by the finite singleton without
    a hull. *)
Corollary finite_infinite_measure_not_regular (R : realType) :
  ~ is_regular_measure (@finite_infinite_measure R _ : set nat -> \bar R).
Proof.
move=> hr.
have h0 : [set 0%N] != (@set0 nat).
  apply/eqP=> he; have hx : [set 0%N] 0%N by []; by rewrite he in hx.
have hf : finite_infinite_measure (R := R) [set 0%N] < +oo.
  by rewrite (@finite_infinite_measure_finite R _ _ h0 (finite_set1 _)) ltry.
have [B hB] := @regular_measure_finite_hull R _ _ (@finite_infinite_measure_is_measure R _) hr [set 0%N] hf.
exact: (@finite_infinite_singleton_no_hull R B hB).
Qed.
