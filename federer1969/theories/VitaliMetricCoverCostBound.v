(** Federer (1969), 3.2.26(2), p. 261: disjoint
    small balls, supplied by the Vitali theorem, bound the
    sum of the costs of the corresponding thin convex
    generators by the source mass. Keep the abstract covering
    laws separate from the geometric tube estimates. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit MeasureAlmostBasic
  MeasureCountableAdditivity BorelRegularMeasureUP TopologicalBorel CountablyClosedFamilyUP
  CoveringRelationUP MetricDiameter MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleCutoffCost
  MetricScaleIndexedCover NonnegativeSum NonnegativeSumScale.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [vitali_metric_cover_cost_bound]: the disjoint
    covering and summed-cost step in 3.2.26(2), p. 261,
    using 2.8.15–18, pp. 150–152. Geometry must
    prove the fine subrelation and the actual generator cost
    estimate; this lemma assumes no measure equality on
    rectifiable sets. Repeated generators are permitted. *)
Theorem vitali_metric_cover_cost_bound (R:realType) (X:metricType R) (J:choiceType)
    (j0:J) (S:J->set X) (c:J->\bar R) (delta: \bar R)
    (mu nu:set X->\bar R) (W Z:set X)
    (V C:X->set X->Prop) (a:R):
  is_measure mu ->is_borel_regular_measure mu ->is_vitali_relation mu V ->
  is_metric_scale_envelope S c delta nu ->(forall j,0<=c j) ->(0<a)%R ->
  mu (W `\` Z)=0 ->
  (forall A,A `<=` W ->mu A=0 ->nu A=0) ->
  (forall x B,C x B ->V x B) ->
  (forall x,Z x ->covering_relation_fine_at C x) ->
  (forall x B,C x B ->exists j,
    W `&` B `<=` S j /\extended_metric_diameter (S j)<=delta /\c j<=a%:E*mu B) ->
  nu W<=a%:E*mu setT.
Proof.
move=>hMu hRegular hV hNu hc ha hOutside hNull hCV hFine hCost.
have hNuMeasure:=metric_scale_envelope_is_measure hNu hc.
have [G [hG [hCount [hDisjoint hRemainder]]]]:=vitali_relation_selection hV hCV hFine.
pose U:=\bigcup_(B in G) B.
have hMuR:mu (W `\` U)=0.
  have hUnion:=measure_null_union hMu hOutside hRemainder.
  apply:(measure_null_subset hMu _ hUnion)=>x [hx hn].
  have [hz|hz]:=pselect (Z x); [right|left]; by split.
have hNuR:nu (W `\` U)=0:=hNull (W `\` U) (fun x hx=>hx.1) hMuR.
have hChoice B:exists j,G B ->
    W `&` B `<=` S j /\extended_metric_diameter (S j)<=delta /\c j<=a%:E*mu B.
  have [hb|hb]:=pselect (G B).
  - have [x [_ hx]]:=hG B hb; have [j hj]:=hCost x B hx.
    by exists j.
  - exists j0=>h; exfalso; exact:hb h.
have [k hk]:=choice hChoice.
have hCover:W `&` U `<=` \bigcup_(B in G) S (k B).
  move=>x [hx [B hb hBx]]; exists B; first exact hb.
  exact:(hk B hb).1 x (conj hx hBx).
have hBound:=@metric_scale_envelope_indexed_cover R X J
  [the choiceType of (set X:Type)] S c delta nu hNu (W `&` U) G k hCount
  (fun B _=>hc (k B)) (fun B hb=>(hk B hb).2.1) hCover.
have hSum:nonnegative_sum G (fun B=>c (k B))<=a%:E*mu setT.
  apply:le_trans (nonnegative_sum_mono (fun B hb=>(hk B hb).2.2)) _.
  rewrite (@nonnegative_sum_scale R [the choiceType of (set X:Type)] G mu a
    (ltW ha) (fun B _=>measure_nonnegative hMu B)).
  apply:lee_wpmul2l; first by rewrite lee_fin; exact:ltW ha.
  have hMeas B:G B ->measure_measurable mu B.
    move=>hb; apply:(borel_regular_borel_measurable hMu hRegular).
    apply:(vitali_relation_borel hV).
    have [x [_ hx]]:=hG B hb; exists x; split; first exact I.
    exact:hCV x B hx.
  have hApart B D:G B ->G D ->B!=D ->forall x,B x ->D x ->False.
    move=>hb hd hBD x hx hDx.
    have hNe:B<>D by move=>hEq; by rewrite hEq eqxx in hBD.
    have hEmpty:=hDisjoint B D hb hd hNe.
    have hBoth:(B `&` D) x by split.
    by rewrite hEmpty in hBoth.
  rewrite -(@measure_countable_disjoint_additivity R (Choice.clone X _)
    [the choiceType of (set X:Type)] mu hMu G id hCount hMeas hApart).
  exact (@measure_mono R (Choice.clone X _) mu hMu U setT (subsetT U)).
have hSplit:=measure_split_upper hNuMeasure W U.
rewrite hNuR adde0 in hSplit.
exact:(le_trans hSplit (le_trans hBound hSum)).
Qed.
