(** Federer (1969), 2.2.3, pp. 61–62, and
    the compact reduction in 2.10.26, p. 190:
    a countably finite measurable set in a proper metric
    space has an increasing compact core with null
    remainder. This supports 3.2.46, p. 282. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets cardinality constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostBasic
  CountablyMeasurableUP CountablyMeasurableSequences BorelRegularMeasureUP
  LipschitzFunctionCompact ProperMetricCompactApproximation
  CountableFamilySequence SetSequenceDisjointification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [proper_metric_sigma_finite_compact_core]:
    countable finite-measure exhaustion followed by the
    compact reduction of 2.10.26, p. 190,
    supporting 3.2.46, p. 282. Every compact
    lies in the original set and the discarded set
    is actually null. No false null difference of
    an arbitrary nonmeasurable hull is asserted. *)
Theorem proper_metric_sigma_finite_compact_core (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (a : X) (S : set X) :
  is_measure mu -> is_borel_regular_measure mu -> metric_boundedly_compact X ->
  measure_countably_measurable mu S ->
  exists K : nat -> set X, (forall n, compact (K n)) /\
    (forall n, K n `<=` S) /\ (forall n j, (n<=j)%N -> K n `<=` K j) /\
    mu (S `\` (\bigcup_n K n))=0.
Proof.
move=> hMu hRegular hProper hCount.
have [F [hF hFm]] := (@countably_measurable_sequence_iff R X mu hMu S).1 hCount.
have hFiniteCore n := @proper_metric_finite_compact_approximation R X mu hMu hRegular
  (F n) a hProper (hFm n).1 (hFm n).2.
pose C n := projT1 (cid (hFiniteCore n)).
have hC n := projT2 (cid (hFiniteCore n)).
pose D (p : nat*nat) := C p.1 p.2.
have hCompact p : compact (D p) := (hC p.1).1 p.2.
have hSubset p : D p `<=` S.
  move=> x hx; rewrite hF; exists p.1; first exact Logic.I; exact:(hC p.1).2.1 p.2 x hx.
have hRemainder : mu (S `\` (\bigcup_p D p))=0.
  apply:(measure_null_subset hMu _
    (@measure_null_countable_union R X nat mu hMu setT
      (fun n=>F n `\` (\bigcup_j C n j)) (countableP _)
      (fun n _=>(hC n).2.2.2))).
  move=> x [hx hOutside]; rewrite hF in hx; have [n _ hxn] := hx.
  exists n; first exact Logic.I; split; first exact hxn.
  move=> [j _ hxj]; apply:hOutside; by exists (n,j).
have [E [hE hUnion]] := @countable_family_as_sequence X [the choiceType of ((nat*nat)%type : Type)]
  setT D (countableP _).
have hEc n : compact (E n).
  case:(hE n)=> [->|[p [_ ->]]]; [exact:compact0 | exact:hCompact].
have hES n : E n `<=` S.
  case:(hE n)=> [->|[p [_ ->]]]; [by move=> x [] | exact:hSubset].
pose K n := set_sequence_prefix E n.
have hKCompact n : compact (K n).
  elim:n=> [|n ih]; first by rewrite /K set_sequence_prefix_zero; exact:compact0.
  rewrite /K set_sequence_prefix_succ; exact:compactU ih (hEc n).
have hKSubset n : K n `<=` S by move=> x [j hj hx]; exact:hES j x hx.
have hIncreasing n j (hnj : (n<=j)%N) : K n `<=` K j.
  move=> x [i hi hx]; exists i; last exact hx; exact:leq_trans hi hnj.
have hKUnion : (\bigcup_n K n)=\bigcup_n E n.
  apply/seteqP; split=> x.
  - move=> [n _ [j hj hx]]; by exists j.
  - move=> [j _ hx]; exists j.+1; first exact Logic.I.
    exists j; last exact hx; exact:ltnSn.
exists K; split; first exact hKCompact; split; first exact hKSubset.
split; first exact hIncreasing.
by rewrite hKUnion hUnion.
Qed.
