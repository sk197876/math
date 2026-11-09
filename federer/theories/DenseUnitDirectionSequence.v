(** Federer (1969), 3.3.18, p. 301: actual countably
    many unit directions for the converse counterexample. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals topology.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric UnitSphereSpace
  EuclideanMetricSeparability MetricSubsetBackground MetricSubsetSeparability
  SeparablePointSequenceUP SeparablePointSequenceSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [dense_unit_direction_sequence_exists]: supporting
    countable radial directions for the false-converse assertion
    in Federer 3.3.18, p. 301. Actual hereditary Euclidean metric
    separability and the existing sealed dense-sequence laws give
    unit vectors meeting EVERY original open set that meets the
    unit sphere. The sequence is only an existential local witness. *)
Theorem dense_unit_direction_sequence_exists (R:realType) n (hn:(0<n)%N):
  exists v:nat->inner_metric_space (@euclidean_inner_productP R n),
    (forall j,inner_norm (@euclidean_inner_productP R n) (v j)= 1%R) /\
    forall U:set (inner_metric_space (@euclidean_inner_productP R n)),
      open U ->(exists u,inner_norm (@euclidean_inner_productP R n) u= 1%R /\U u) ->
      exists j,U (v j).
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose S:=@euclidean_unit_sphere_set R n.
pose Y:=@metric_subset R [the metricType R of X] S.
pose y0:Y:=@euclidean_unit_sphere_point R n hn.
have [D [hc hd]]:=@metric_subset_separable R [the metricType R of X] S (@euclidean_metric_separable R n).
pose f:=@SeparablePointSequence.value R Y y0 D hc hd.
have hSequence:=@SeparablePointSequence.laws R Y y0 D hc hd.
exists (fun j=>(val (f j):X)); split.
- move=>j; exact:set_valP (f j).
- move=>U hU [u [hUnit hu]].
  pose V:set Y:=[set y|U (val y)].
  have hV:open V.
    apply:open_comp _ hU=>y _; exact:metric_subset_inclusion_continuous y.
  have hNonempty:V!=set0.
    exists (@exist X (fun x=>x \in S) u (mem_set hUnit)); exact:hu.
  have [y [hy [j _ hF]]]:=hSequence.2 V hNonempty hV.
  exists j; change (U (val (f j))).
  change (f j=y) in hF; rewrite hF; exact:hy.
Qed.
