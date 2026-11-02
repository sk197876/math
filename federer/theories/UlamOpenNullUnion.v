(** Federer (1969), 2.2.16, pp. 71–72: an open null family with Ulam index
    cardinality has null union under a finite metric measure whose open sets
    are measurable. Refine it into countably many uniformly separated closed
    families and apply the second Ulam property of 2.1.6. Measurability of
    all subfamily unions follows from closedness, without assuming every
    subset of the open union measurable. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum MeasureUP MeasureBasic MeasureFiniteClosure
  MeasureIndexedCover MeasureDisjointFamily UlamCardinalUP UlamNullFamilies
  SeparatedClosedUnions OpenCoverClosedRefinementUP OpenCoverClosedRefinementSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [ulam_indexed_open_null_union]: supporting
    conclusion of the closed-family argument in Federer 2.2.16,
    pp. 71–72, for an arbitrary Ulam-indexed open
    null family. The application to support uses a metric base. *)
Theorem ulam_indexed_open_null_union (R : realType) (X : metricType R)
    (J : choiceType) (mu : set X -> \bar R) (hm : is_measure mu)
    (D : set J) (U : J -> set X) :
  mu setT < +oo -> (forall V, open V -> measure_measurable mu V) ->
  is_ulam_set R D -> (forall j, D j -> open (U j)) ->
  (forall j, D j -> mu (U j) = 0) -> mu (\bigcup_(j in D) U j) = 0.
Proof.
move=> hf hmeas hu ho hz.
pose C := @OpenCoverClosedRefinement.value R X J D U ho.
have hC := @OpenCoverClosedRefinement.laws R X J D U ho.
have hc n j : D j -> closed (C n j).
  exact: (@closed_open_refinement_closed R X J D U C hC n j).
have hs n := @closed_open_refinement_separated R X J D U C hC n.
have hr n : (0 < (((n.+1)%:R : R)^-1))%R by rewrite invr_gt0 ltr0n.
have hclosed V : closed V -> measure_measurable mu V.
  move=> hV; have hh := measure_measurable_complement (hmeas _ (closed_openC hV)).
  by rewrite setCK in hh.
have hzero n : mu (\bigcup_(j in D) C n j) = 0.
  apply: (@ulam_set_null_families R J D hu X J mu D (C n) hm (card_lexx D)).
  - move=> j k hj hk hne; apply/seteqP; split; last by move=> x [].
    move=> x [hxj hxk]; have hh := hs n j k hj hk hne x x hxj hxk.
    rewrite mdistxx in hh; by move: (hr n); rewrite ltNge hh.
  - apply: le_lt_trans _ hf; apply: (@measure_mono R X mu hm _ setT)=> x hx; exact Logic.I.
  - move=> E; apply: hclosed.
    exact: (@uniformly_separated_closed_subfamily_union R X J D (C n)
      (((n.+1)%:R)^-1)%R (hr n) (hc n) (hs n) E).
  - move=> j hj; apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
    have hh := @measure_mono R X mu hm (C n j) (U j)
      (@closed_open_refinement_inside R X J D U C hC n j hj).
    by rewrite (hz j hj) in hh.
rewrite (@closed_open_refinement_cover R X J D U C hC).
apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
have hh := @measure_indexed_cover R X _ mu hm
  (\bigcup_n \bigcup_(j in D) C n j) setT (fun n => \bigcup_(j in D) C n j)
  (@countableP _ (@setT nat)) (fun x hx => hx).
have hz' n : setT n -> mu (\bigcup_(j in D) C n j) = 0 by move=> _; exact: hzero n.
by rewrite (nonnegative_sum_zero hz') in hh.
Qed.
