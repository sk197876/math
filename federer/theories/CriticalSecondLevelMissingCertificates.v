(** Federer (1969), 3.3.20, p. 308:
    the actual two initial Omega certificates after an adjacent-parent reduction. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge EuclideanInnerProduct
  InnerMetric EuclideanIntervalRectangles CriticalSecondLevelIntervals
  CriticalSecondLevelSquareDistances FinitePairedMetricDiameter FiniteCellHitMeasureUP
  FiniteCellHitIndicesLaws MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_second_level_adjacent_missing_certificates]:
    the (2,8,4,11/16) and (2,8,1,7/8)
    original-square certificates of 3.3.20,
    p. 308. Once the eight descendants of
    the missed row are actually missed, injection
    gives their exact count. Four corresponding
    pairs and one outermost pair avoid that row,
    and actual coordinate inequalities prove the gaps.
    The first implication holds under the stronger
    threshold twelve; the book applies it below eleven.
    The adjacent-parent reduction is proved separately. *)
Theorem critical_second_level_adjacent_missing_certificates (R:realType)
    (F:{fset (compact_real_intervals R*compact_real_intervals R)})
    (Q:((bool*bool)*(bool*bool))->(compact_real_intervals R*compact_real_intervals R))
    (b:bool) (T:set (inner_metric_space (@euclidean_inner_productP R 2))):
  injective Q ->(forall k,Q k \in F) ->
  (forall k,val (Q k).1=
    (`[critical_second_level_coordinate R k.1.1 k.2.1,
      critical_second_level_coordinate R k.1.1 k.2.1+1/16]:set (real_line_metric R))) ->
  (forall z:bool*(bool*bool),forall x,
    euclidean_interval_rectangle (Q ((z.1,negb b),z.2)).1 (Q ((z.1,negb b),z.2)).2 x ->~T x) ->
  let missed:=#|` ((F `\` finite_cell_hit_indices F
    (fun P=>euclidean_interval_rectangle P.1 P.2) T)%fset)| in
  ((missed<12)%N ->((11/16:R)%:E<=extended_metric_diameter T)%E) /\
  ((missed<9)%N ->((7/8:R)%:E<=extended_metric_diameter T)%E).
Proof.
move=>hQ hMembers hCoordinates hMissedRow missed.
pose I4:finType:=Finite.clone (bool*bool)%type _.
pose I1:finType:=Finite.clone unit _.
pose C (z:bool*(bool*bool)):=Q ((z.1,negb b),z.2).
pose K:=[fset C z|z:bool*(bool*bool)].
have hCInjective:injective C.
  move=>[p i] [q j] hEqual.
  have h:=hQ _ _ hEqual.
  have hParent:=congr1 (fun k=>k.1.1) h.
  have hChildren:=congr1 snd h.
  rewrite /= in hParent hChildren.
  by rewrite hParent hChildren.
have hKCard:#|` K|=8%N.
  by rewrite /K card_imfset //= -cardE !card_prod !card_bool.
have hK:{subset K<=(F `\` finite_cell_hit_indices F
    (fun P=>euclidean_interval_rectangle P.1 P.2) T)%fset}.
  move=>P /imfsetP[z _ ->];rewrite in_fsetD;apply/andP;split.
  - apply/negP=>/finite_cell_hit_indices_membership[_ [x [hxCell hxT]]].
    exact:hMissedRow z x hxCell hxT.
  - exact:hMembers.
have hNotFlip:forall t:bool,t=negb t ->False by move=>[] /=;discriminate.
have hAvoid p t u:Q ((p,b),(t,u)) \notin K.
  apply/negP=>/imfsetP[z _ hEqual].
  have h:=hQ _ _ hEqual.
  have hBits:b=negb b:=congr1 (fun k=>k.1.2) h.
  exact:hNotFlip b hBits.
pose e (k:(bool*bool)*bool):=Q ((k.2,b),k.1).
have hEInjective:injective e.
  move=>[i t] [j u] hEqual.
  have h:=hQ _ _ hEqual.
  have hIndices:=congr1 snd h.
  have hEnds:=congr1 (fun k=>k.1.1) h.
  rewrite /= in hIndices hEnds.
  by rewrite hIndices hEnds.
have hEndpoints i t:e (i,t) \in F /\e (i,t) \notin K.
  split;first exact:hMembers.
  case:i=>[v w];exact:hAvoid.
have hDistance i p q:
    euclidean_interval_rectangle (e (i,false)).1 (e (i,false)).2 p ->
    euclidean_interval_rectangle (e (i,true)).1 (e (i,true)).2 q ->(11/16:R)<=mdist p q.
  move=>[hp _] [hq _].
  rewrite /e /= (hCoordinates ((false,b),i)) in hp.
  rewrite /e /= (hCoordinates ((true,b),i)) in hq.
  exact:(@critical_second_level_corresponding_child_gap R i.1 p q hp hq).
pose eOuter (k:unit*bool):=Q ((k.2,b),(k.2,false)).
have hOuterInjective:injective eOuter.
  move=>[[] t] [[] u] hEqual.
  have h:=hQ _ _ hEqual.
  have hEnds:=congr1 (fun k=>k.1.1) h.
  rewrite /= in hEnds;by rewrite hEnds.
have hOuterEndpoints i t:eOuter (i,t) \in F /\eOuter (i,t) \notin K.
  split;first exact:hMembers.
  exact:hAvoid.
have hOuterDistance i p q:
    euclidean_interval_rectangle (eOuter (i,false)).1 (eOuter (i,false)).2 p ->
    euclidean_interval_rectangle (eOuter (i,true)).1 (eOuter (i,true)).2 q ->(7/8:R)<=mdist p q.
  move=>[hp _] [hq _].
  rewrite /eOuter /= (hCoordinates ((false,b),(false,false))) in hp.
  rewrite /eOuter /= (hCoordinates ((true,b),(true,false))) in hq.
  exact:(@critical_second_level_outer_child_gap R p q hp hq).
split=>hCount.
- refine (@finite_paired_missing_metric_diameter R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)] _ I4
    F K (fun P=>euclidean_interval_rectangle P.1 P.2) T e (11/16:R)
    hK hEInjective hEndpoints hDistance _).
  by rewrite hKCard /I4 card_prod !card_bool.
- refine (@finite_paired_missing_metric_diameter R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)] _ I1
    F K (fun P=>euclidean_interval_rectangle P.1 P.2) T eOuter (7/8:R)
    hK hOuterInjective hOuterEndpoints hOuterDistance _).
  by rewrite hKCard /I1 card_unit.
Qed.
