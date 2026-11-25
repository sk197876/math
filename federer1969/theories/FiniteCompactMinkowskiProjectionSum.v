(** Federer (1969), 3.2.37, p. 274: the sum of independently
    projected volumes of finitely many disjoint compact source pieces
    is at most the original source's lower Minkowski content. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanBallVolume MinkowskiContents MinkowskiContentsBasic
  LowerMinkowskiProjectionBound FiniteCompactTubeSeparation MetricOpenThickening
  MetricOpenThickeningClosure MeasureUP MeasureBasic MeasureFiniteAdditivity
  BorelRegularMeasureUP TopologicalBorel PositiveRadiusLowerApproximation CoordinateProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_compact_projected_volume_lower_minkowski]:
    the finite-compact-family comparison in Federer 3.2.37, p. 274.
    Each piece has its own actual orthogonal projection. Uniform
    separation gives disjoint positive-radius tubes; finite measure
    additivity and the actual fibre estimate precede the lower limit.
    The containing source is arbitrary and all values may be infinite. *)
Theorem finite_compact_projected_volume_lower_minkowski (R:realType) n m
    (I:choiceType) (B:{fset I})
    (K:I->set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:I->{linear R_n R n->R_n R m})
    (A:set (inner_metric_space (@euclidean_inner_productP R n))):
  (m<=n)%N ->(forall i,i \in B ->compact (K i)) ->
  (forall i,i \in B ->K i `<=` A) ->(forall i,i \in B ->O_star (p i)) ->
  (forall i j,i \in B ->j \in B ->i!=j ->forall x,K i x ->K j x ->False) ->
  (\sum_(i<-B) @euclidean_lebesgue_measure R m (p i @` K i))<=lower_minkowski_content m A.
Proof.
move=>hmn hK hKA hp hDisjoint.
have [e [he hSeparated]]:=finite_compact_open_tubes_separated hK hDisjoint.
apply:positive_radius_lower_eventual_bound he _=>r hr.
pose X:=[the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
pose mu:=@euclidean_lebesgue_measure R n.
pose T:=fun i=>metric_open_thickening (K i) r.
pose d:=(euclidean_unit_ball_volume R (n-m)*r^+(n-m))%R.
have hPositive:(0<d)%R:=minkowski_tube_denominator_positive n m (andP hr).1.
have hMeasurable i:measure_measurable mu (T i).
  apply:(@borel_regular_borel_measurable R X mu (euclidean_lebesgue_is_measure R n)
    (euclidean_lebesgue_borel_regular R n)).
  exact:open_borel_set (metric_open_thickening_open (K i) r).
have hMass:mu (\bigcup_(i in [set` B]) T i)=\sum_(i<-B) mu (T i).
  apply:(@measure_finite_disjoint_additivity R X I mu (euclidean_lebesgue_is_measure R n) T B).
  - by move=>i _; exact:hMeasurable.
  - exact:hSeparated r hr.
have hTube:(\sum_(i<-B) minkowski_tube_quotient m (K i) r)<=minkowski_tube_quotient m A r.
  rewrite /minkowski_tube_quotient -ge0_sume_distrl; last first.
  - move=>i _; exact:(@measure_nonnegative R X mu (euclidean_lebesgue_is_measure R n) _).
  - rewrite -hMass; apply:lee_wpmul2r; last first.
    + apply:(@measure_mono R X mu (euclidean_lebesgue_is_measure R n))=>x [i hi hx].
      exact:(@metric_open_thickening_monotone R X (K i) A r (hKA i hi) x hx).
    + rewrite inve_ge0 lee_fin; exact:ltW hPositive.
apply:le_trans _ hTube.
rewrite !big_seq; apply:lee_sum=>i hi.
exact:minkowski_tube_projection_bound hmn (hp i hi) (andP hr).1.
Qed.

(** Source for [finite_type_compact_projection_lower_minkowski]:
    the finite-index version of the compact-family sum in Federer
    3.2.37, p. 274. Empty index types are retained. *)
Corollary finite_type_compact_projection_lower_minkowski (R:realType) n m
    (I:finType) (K:I->set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:I->{linear R_n R n->R_n R m})
    (A:set (inner_metric_space (@euclidean_inner_productP R n))):
  (m<=n)%N ->(forall i,compact (K i)) ->(forall i,K i `<=` A) ->
  (forall i,O_star (p i)) ->
  (forall i j,i!=j ->forall x,K i x ->K j x ->False) ->
  (\sum_i @euclidean_lebesgue_measure R m (p i @` K i))<=lower_minkowski_content m A.
Proof.
move=>hmn hK hKA hp hDisjoint.
have h:=@finite_compact_projected_volume_lower_minkowski R n m I [fset i in enum I] K p A
  hmn (fun i _=>hK i) (fun i _=>hKA i) (fun i _=>hp i)
  (fun i j _ _=>hDisjoint i j).
have hPerm:perm_eq ([fset i in enum I]:seq I) (enum I).
  apply:uniq_perm; [exact:fset_uniq|exact:enum_uniq|].
  by move=>i; rewrite in_fset.
have hEq:(\sum_(i<-[fset i in enum I]) @euclidean_lebesgue_measure R m (p i @` K i))=
    (\sum_i @euclidean_lebesgue_measure R m (p i @` K i)).
  rewrite -big_enum; exact:perm_big hPerm.
by rewrite hEq in h.
Qed.
