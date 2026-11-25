(** Federer (1969), 2.5.10, p. 101, final paragraph: every Radon measure
    satisfies the disjoint finite-measure decomposition condition. We state
    and prove existence of a family satisfying the abstract condition,
    including spaces of non-countably-measurable total measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureAlmostBasic RadonMeasureUP RadonBorelRegularity
  MaximalDisjointFamilyUP MaximalDisjointFamily RadonCompactSupport RadonCompactMeetingFamily
  RadonMaximalCompactCover RadonCountableCompactCover FiniteMeasureDecompositionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [radon_measure_finite_decomposition]: direct formalisation of
    the Radon assertion in Federer 2.5.10, p. 101 The actual pieces are
    compact, pairwise disjoint and finite in measure; each arbitrary
    finite-measure set is almost covered by a countable subfamily. No
    countability of the whole space is assumed. *)
Theorem radon_measure_finite_decomposition (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu) (hr : is_radon_measure mu) :
  exists G : set (set T), (forall K, G K -> compact K) /\
    is_finite_measure_decomposition mu G (fun K => K).
Proof.
pose G := maximal_disjoint_family (is_positive_compact_piece mu).
have hG := maximal_disjoint_family_specification (is_positive_compact_piece mu).
have hpiece K : G K -> is_positive_compact_piece mu K.
  exact: (@maximal_disjoint_family_members T _ _ hG K).
have hdis := maximal_disjoint_family_disjoint hG.
exists G; split; first by move=> K hk; exact: (hpiece K hk).1.
split.
- move=> K hk; split.
  + exact (@radon_compact_measurable R T mu hm hr K (hpiece K hk).1).
  + exact (@radon_compact_finite R T mu hr K (hpiece K hk).1).
- split=> //; move=> A hA.
  have [K [hK hcover]] := radon_finite_countable_compact_cover hm hr hA.
  pose C n := compact_meeting_family G (K n).
  have hcount n : countable (C n) := radon_compact_meeting_countable hm hr hpiece hdis (hK n).
  have hnull n : mu (K n `\` (\bigcup_(L in C n) L))=0.
    exact (@radon_maximal_compact_almost_cover R T mu hm hr G (K n) hG (hK n)).
  exists (\bigcup_n C n); split.
  + move=> L [n _ [hl _]]; exact: hl.
  + split; first exact: bigcup_countable (countableP setT) (fun n _ => hcount n).
    have hn := @measure_null_countable_union R T [the choiceType of (nat : Type)] mu hm setT
      (fun n => K n `\` (\bigcup_(L in C n) L)) (countableP setT) (fun n _ => hnull n).
    have hh := measure_null_union hm hcover hn.
    apply: (@measure_null_subset R T mu hm _ _ _ hh)=> x [hx hout].
    case: (pselect ((\bigcup_n K n) x))=> hu; last by left.
    have [n _ hxn] := hu; right; exists n=> //; split=> //.
    move=> [L hl hxl]; apply: hout; exists L=> //; by exists n.
Qed.
