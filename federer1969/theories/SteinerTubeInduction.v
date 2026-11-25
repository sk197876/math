(** Federer (1969), 3.2.35, p. 272:
    close the dimension induction by coarea,
    the evaluated level polynomial and exact
    additive volume splitting. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP
  MetricSetDistanceUP MetricDistanceClosureLaws ClosedSetDistanceCoarea ConvexTubeVolumeSplitting
  SteinerTubePolynomial SteinerDistanceLevelIntegral FullDimensionIntegralGauge IntegralGeometricGauge
  EuclideanBallVolume EuclideanLebesgueDimensions MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [integral_geometric_gauge_proof_irrelevant]:
    dimension-guard bookkeeping for the original
    intrinsic-volume coefficients of Federer
    3.2.35, p. 271. Different proofs of
    the same dimension inequality leave the
    existing gauge unchanged. *)
Lemma integral_geometric_gauge_proof_irrelevant (R:realType) n m (h1 h2:(m<=n)%N) t
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  @integral_geometric_gauge R n m h1 t S=@integral_geometric_gauge R n m h2 t S.
Proof. by have ->:h1=h2:=Prop_irrelevance _ _. Qed.

(** Source for [steiner_tube_induction_step]: the
    complete induction step for Steiner's formula,
    Federer 3.2.35, p. 272. The actual
    distance to closure S has the original
    distance laws, so 3.2.34 identifies the
    positive strip with the proved level integral.
    Exact additive splitting restores the original
    source volume, which is the full-degree
    intrinsic volume. No source measurability,
    interior, positive source volume or additional
    geometric theorem is assumed. *)
Theorem steiner_tube_induction_step (R:realType) k:
  (forall (A:set (inner_metric_space (@euclidean_inner_productP R k))) e,
    A!=set0 ->is_inner_convex A ->metric_set_bounded A ->is_metric_set_distance A e ->
    is_steiner_tube_volume A e) ->
  forall (S:set (inner_metric_space (@euclidean_inner_productP R k.+1))) d,
    S!=set0 ->is_inner_convex S ->metric_set_bounded S ->is_metric_set_distance S d ->
    is_steiner_tube_volume S d.
Proof.
move=>hIH S d hNonempty hS hBound hD r hr.
pose X:=inner_metric_space (@euclidean_inner_productP R k.+1).
have hClosureNonempty:closure S!=set0.
  have [a ha]:=hNonempty; exists a; exact:subset_closure ha.
have hCoarea:=@federer_3_2_34 R k.+1 (closure S) d (0%R:R) r (ltn0Sn k)
  (@closed_closure [the topologicalType of X] S) hClosureNonempty
  (metric_distance_closure_laws hD) ltac:(by rewrite lexx hr).
rewrite subn1 in hCoarea.
have hLevelIntegral:=@steiner_distance_level_integral R k S d r hIH hNonempty hS hBound hD hr.
have hStrip:=measure_integral_unique hCoarea hLevelIntegral.
have hSplit:=@convex_tube_volume_splitting R k.+1 S d r hNonempty hS hD hr.
rewrite hSplit hStrip /steiner_tube_polynomial [RHS]big_ord_recr subnn euclidean_unit_ball_volume0 expr0 mulr1 mule1.
rewrite (@equal_dimension_integral_geometric_gauge R k.+1 _ 1 S (lexx 1)).
rewrite [euclidean_lebesgue_measure k.+1 S+_]addeC.
congr (_+euclidean_lebesgue_measure k.+1 S); apply:eq_bigr=>i _.
congr (_*_); exact:integral_geometric_gauge_proof_irrelevant.
Qed.
