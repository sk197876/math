(** Federer (1969), 2.10.24, p. 187: supporting summable-error construction
    of the increasing Borel sets B_j covering the positive support almost
    everywhere. A point lying in infinitely many exceptional sets belongs to
    every tail union; their measure bounds tend to zero. Only the project's
    measure and nonnegative-sum laws are used. Source context:
    WeightedMetricEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureIndexedCover NonnegativeSum NonnegativeSeriesTails
  ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_summable_exceptional_limsup_null]: supporting
    summable-error implication for the B_j choice
    in 2.10.24, p. 187. The exceptional
    sets need not themselves be measurable, and
    no finite total mass is assumed. *)
Theorem measure_summable_exceptional_limsup_null (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (E : nat -> set X) :
  is_measure mu -> nonnegative_sum setT (fun n=>mu (E n))< +oo ->
  mu (\bigcap_N \bigcup_(n in [set n | (N<=n)%N]) E n)=0.
Proof.
move=> hm hs.
pose Z := \bigcap_N \bigcup_(n in [set n | (N<=n)%N]) E n.
have hbound : mu Z<=0.
  apply: (@extended_upper_bound_from_scaled_errors R (mu Z) 0%R 1%R (@ler01 R))=> e he.
  have [N hN] := nonnegative_series_tail_small (fun n=>measure_nonnegative hm (E n)) hs he.
  have hcover : Z `<=` \bigcup_(n in [set n | (N<=n)%N]) E n.
    move=> x hx; exact: hx N Logic.I.
  have hh := @measure_indexed_cover R X [the choiceType of (nat : Type)] mu hm Z
    [set n | (N<=n)%N] E (sub_countable (subset_card_le (fun n (_ : (N<=n)%N)=>Logic.I)) (countableP _)) hcover.
  rewrite mul1r add0r; exact: le_trans hh (ltW hN).
apply/eqP; by rewrite eq_le hbound (measure_nonnegative hm Z).
Qed.
