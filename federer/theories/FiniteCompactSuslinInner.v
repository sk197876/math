(** Federer (1969), 2.10.48, p. 206: the supremum of the finite compact
    masses is approached by an increasing compact sequence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import FiniteCompactMassUP FiniteCompactMassSealed MeasureUP MeasureBasic MeasureSplit MeasureFiniteClosure MeasureFiniteAdditivity MeasureCountableClosure MeasureContinuityBelow ExtendedRealLimitBounds ExtendedRealBoundsUP SuslinSetUP BorelSuslinImages BorelClosedProjection TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_compact_suslin_mass_bound]: supporting
    measure-theoretic argument of 2.10.48, p. 206. The
    positive finite compact subset premise is discharged using
    2.10.23 and 2.10.47 in the Euclidean application. *)
Theorem finite_compact_suslin_mass_bound (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (S : set X) (M : R) :
  is_measure mu -> (forall C, compact C -> measure_measurable mu C) ->
  (forall T, is_suslin_set R T -> 0<mu T ->
    exists B, [/\ compact B, B `<=` T, 0<mu B & mu B< +oo]) ->
  is_suslin_set R S ->
  (forall C, compact C -> C `<=` S -> mu C< +oo -> mu C<=M%:E) -> mu S<=M%:E.
Proof.
move=> hm hmeas hpos hS hb.
pose F := @FiniteCompactMass.sequence R X mu S M hm hb.
have [hF hmono hcofinal] := @FiniteCompactMass.laws R X mu S M hm hb.
pose U := \bigcup_n F n.
have hFm n : measure_measurable mu (F n).
  have [hC _ _] := hF n; exact: hmeas.
have hUm : measure_measurable mu U := measure_measurable_sequence_union hm hFm.
have hUS : U `<=` S by move=> x [n _ hx]; have [_ hsub _] := hF n; exact: hsub.
have hUb : mu U<=M%:E.
  apply: (extended_order_limit_upper_bound (measure_continuity_below hm hFm hmono).2)=> n.
  have [hC hCS hfin] := hF n; exact (hb (F n) hC hCS hfin).
have hUf : mu U \is a fin_num.
  rewrite ge0_fin_numE; last exact (@measure_nonnegative R X mu hm U).
  exact: le_lt_trans hUb (ltry M).
have hBU : borel_set U.
  apply: borel_set_countable_union (countableP setT) _=> n _.
  have [hC _ _] := hF n; exact: closed_borel_set (compact_closed (@metric_hausdorff R X) hC).
have hT : is_suslin_set R (S `\` U).
  exact: suslin_binary_intersection hS (metric_borel_suslin (borel_set_complement hBU)).
have hzero : mu (S `\` U)=0.
  apply/eqP; rewrite eq_le (@measure_nonnegative R X mu hm (S `\` U)) andbT leNgt; apply/negP=> hpositive.
  have [B [hBc hBT hBp hBf]] := hpos _ hT hpositive.
  have hBm : measure_measurable mu B := hmeas _ hBc.
  have hBS : B `<=` S by move=> x hx; exact: (hBT x hx).1.
  have hdis : forall x, U x -> B x -> False by move=> x hx hb'; exact: (hBT x hb').2.
  pose G n := F n `|` B.
  have hGm n : measure_measurable mu (G n) := measure_measurable_union hm (hFm n) hBm.
  have hGmono : forall n m, (n<=m)%N -> G n `<=` G m.
    move=> n m hnm x [hx|hx]; [left; exact: hmono n m hnm x hx|by right].
  have hGb n : mu (G n)<=mu U.
    have [hC hCS hfin] := hF n.
    apply: hcofinal.
    - exact: compactU hC hBc.
    - by move=> x [hx|hx]; [exact: hCS|exact: hBS].
    - have hcov := @measure_binary_cover R X mu hm (G n) (F n) B (fun x hx=>hx).
      exact: le_lt_trans hcov (lte_add_pinfty hfin hBf).
  have he : (\bigcup_n G n)=U `|` B.
    apply/seteqP; split.
    - move=> x [n _ [hx|hx]]; [left; by exists n|by right].
    - move=> x [[n _ hx]|hx]; [exists n=> //; by left|exists 0%N=> //; by right].
  have hbound := extended_order_limit_upper_bound (measure_continuity_below hm hGm hGmono).2 hGb.
  rewrite he (measure_disjoint_union hUm hdis) in hbound.
  have hstrict : mu U<mu U+mu B by rewrite -{1}[mu U]adde0 lteD2lE.
  have hbad := lt_le_trans hstrict hbound; by rewrite ltxx in hbad.
have hsplit := hUm S.
have he : S `&` U=U.
  apply/seteqP; split=> [x [_ hx]|x hx] //; by split=> //; exact: hUS.
by rewrite hsplit he hzero adde0.
Qed.

(** Source for [finite_compact_suslin_supremum]: the abstract
    least-upper-bound argument of 2.10.48, p. 206. Empty
    sets and infinite values are retained, without sigma-finiteness. *)
Theorem finite_compact_suslin_supremum (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (S : set X) :
  is_measure mu -> (forall C, compact C -> measure_measurable mu C) ->
  (forall T, is_suslin_set R T -> 0<mu T ->
    exists B, [/\ compact B, B `<=` T, 0<mu B & mu B< +oo]) ->
  is_suslin_set R S -> is_extended_real_supremum (finite_compact_mass_values mu S) (mu S).
Proof.
move=> hm hmeas hpos hS; constructor.
- move=> b [C [hC hCS hfin ->]]; exact (@measure_mono R X mu hm C S hCS).
- move=> b hb; case: b hb=> [r| |] hb; [|exact: leey|].
  + apply: finite_compact_suslin_mass_bound hm hmeas hpos hS _=> C hC hCS hfin.
    apply: hb; exists C; by split.
  + have h0 : finite_compact_mass_values mu S 0.
      exists set0; split; [exact: compact0|by move=> x []|by rewrite (measure_empty hm) ltry|exact: esym (measure_empty hm)].
    have hbad := lt_le_trans (ltNyr (0%R : R)) (hb _ h0); by rewrite ltxx in hbad.
Qed.
