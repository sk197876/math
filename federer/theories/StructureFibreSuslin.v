(** Federer (1969), 3.3.3, p. 288: the accumulation
    locus of the original punctured affine fibres is Suslin.
    Follow the printed projection of S_i and countable
    intersection proof using the existing complete separable
    Euclidean and orthogonal-projection parameter spaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets functions cardinality reals topology.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerNorm
  EuclideanProjectionSpace EuclideanProjectionMetric EuclideanMetricCompleteness
  EuclideanMetricSeparability CompleteMetricUP MetricProductBackground
  MetricProductCompleteness MetricProductSeparability TopologicalProductMaps
  SuslinSetUP SuslinSequenceClosure BorelImageMeasurability
  StructureFibreAccumulation StructureFibreIncidence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_fibre_accumulation_suslin]: all
    of the assertion of Federer 3.3.3, p. 288.
    Actual S_i project to Suslin parameter sets; their
    countable intersection is exactly the original closure
    locus by the cofinal metric-neighbourhood criterion. *)
Theorem structure_fibre_accumulation_suslin (R:realType) n m (hmn:(m<=n)%N)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_suslin_set R A ->is_suslin_set R (structure_fibre_accumulation hmn A).
Proof.
move=>hA.
pose E:=inner_metric_space (@euclidean_inner_productP R n).
pose P:=orthogonal_projection_metric_space R n m.
pose Q:=[the metricType R of metric_product E P].
pose T:=[the metricType R of metric_product E Q].
have hQc:is_complete_metric_space Q.
  exact:(@complete_metric_product R E P (@euclidean_metric_complete R n)
    (@orthogonal_projection_metric_complete R n m)).
have hQs:exists D:set Q,countable D /\ dense D.
  exact:(@separable_metric_product R E P (@euclidean_metric_separable R n)
    (@orthogonal_projection_metric_separable R n m)).
have hTc:is_complete_metric_space T:=@complete_metric_product R E Q (@euclidean_metric_complete R n) hQc.
have hTs:exists D:set T,countable D /\ dense D:=
  @separable_metric_product R E Q (@euclidean_metric_separable R n) hQs.
pose S i:set T:=structure_near_fibre_incidence (m:=m) A i.
have hSi i:is_suslin_set R (S i):=@structure_near_fibre_incidence_suslin R n m A i hA.
have hImage i:is_suslin_set R ((@snd E Q) @` S i).
  exact:(@continuous_suslin_image R T Q (@snd E Q) (S i) hTc hTs
    (@metric_hausdorff R Q) (@second_projection_continuous E Q) (hSi i)).
have he:(structure_fibre_accumulation hmn A:set Q)=
    \bigcap_i ((@snd E Q) @` S i).
  apply/seteqP; split=>z.
  - move/(structure_fibre_accumulation_reciprocals hmn A z)=>h i _.
    have [x [hx [hEq hNear]]]:=h i.
    exists (x,z)=>//; split=>//; split=>//.
    by rewrite linearB hEq subrr.
  - move=>h; apply/(structure_fibre_accumulation_reciprocals hmn A z)=>i.
    have [[x q] [hx [hNear hZero]] hq]:=h i Logic.I.
    change (q=z) in hq; subst q.
    exists x; split=>//; split=>//.
    by move/eqP:hZero; rewrite linearB subr_eq0=>/eqP.
rewrite he; exact:(suslin_sequence_intersection hImage).
Qed.

(** Source for [federer_3_3_3]: direct numbered statement
    of Federer 3.3.3, p. 288, for the actual original
    kernel-plane closure locus and every Suslin source A. *)
Theorem federer_3_3_3 (R:realType) n m (hmn:(m<=n)%N)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_suslin_set R A ->is_suslin_set R (structure_fibre_accumulation hmn A).
Proof. exact:structure_fibre_accumulation_suslin. Qed.
