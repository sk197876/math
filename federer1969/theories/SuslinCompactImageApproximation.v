(** Federer (1969), 3.2.37, p. 274: compact source pieces in the
    projected-volume supremum. Expand the appeal to 2.10.8 by the
    continuous Suslin parametrization of 2.2.10 and the sealed pruning
    of 2.2.12. Compactness is obtained in the source, not merely in
    its projected image. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import CompleteMetricUP SuslinSetUP SuslinParametrisation
  SequenceSpace SequenceBoxes ContinuousClosedGraph MeasureUP MeasureBasic
  RegularMeasureUP BorelRegularMeasureUP TopologicalBorel MeasurePruningSealed
  MeasurePruningUP PruningClosedProjectionLimit PruningClosedLimitMeasure
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_measure_suslin_compact_image_approximation]:
    supporting compact-source approximation for the finite family in
    Federer 3.2.37, p. 274. For a finite Borel regular target measure,
    compact subsets of a Suslin source approximate its entire continuous
    image from below. Independent pruning laws yield a local coordinate
    box; its source image is compact and stays inside the original S. *)
Theorem finite_measure_suslin_compact_image_approximation (R:realType)
    (X:metricType R) (Y:topologicalType) (f:X->Y)
    (mu:set Y->\bar R) (S:set X) (e:R):
  is_complete_metric_space X -> (exists D:set X,countable D /\ dense D) ->
  hausdorff_space Y -> continuous f -> is_measure mu ->
  is_borel_regular_measure mu -> mu setT< +oo -> is_suslin_set R S -> (0<e)%R ->
  exists K, compact K /\ K `<=` S /\ mu (f @` S)-(e/2)%:E<=mu (f @` K).
Proof.
move=>hX hSep hY hf hm hr hFinite hS he.
case:(pselect (S!=set0))=>[hNonempty|hEmpty]; last first.
- have hZero:S=set0.
    apply/seteqP; split=>[x hx|x []]; exfalso; apply:hEmpty; by exists x.
  exists set0; split; first exact:compact0.
  split; first by move=>x [].
  rewrite hZero !image_set0 (measure_empty hm) sub0e.
  by rewrite oppe_le0 lee_fin divr_ge0 //; exact:ltW he.
- have [h [hh hImage]]:=@nonempty_suslin_sequence_parametrisation R X S hX hSep hS hNonempty.
  pose g:=fun z:positive_sequence_space R=>f (h z).
  have hg:continuous g by move=>z; exact:continuous_comp (hh z) (hf (h z)).
  pose Z:set (Y*positive_sequence_space R):=[set p|p.1=g p.2].
  have hZ:closed Z:=continuous_map_closed_graph hY hg.
  have hZImage:fst @` Z=f @` S.
    apply/seteqP; split.
    + move=>y [[z a] hz <-]; exists (h a).
      * rewrite -hImage; by exists a.
      * exact:esym hz.
    + move=>y [x hx <-]; rewrite -hImage in hx.
      have [a _ ha]:=hx; exists (f x,a)=>//.
      change (f x=f (h a)); by rewrite ha.
  pose choice:=@MeasurePruning.value R Y mu hm (borel_regular_is_regular hm hr) hFinite e he Z.
  have hp:=@MeasurePruning.laws R Y mu hm (borel_regular_is_regular hm hr) hFinite e he Z.
  pose K:=h @` (@sequence_coordinate_box R choice.1).
  have hK:compact K.
    exact:(@continuous_compact [the topologicalType of positive_sequence_space R] X
      h (@sequence_coordinate_box R choice.1) (continuous_subspaceT hh)
      (@sequence_coordinate_box_compact R choice.1)).
  have hKS:K `<=` S.
    move=>x [a _ <-]; rewrite -hImage; by exists a.
  have hLower:=@pruned_closed_limit_measure_lower_bound R Y mu hm Z e choice.1 choice.2
    (fun C hC=>borel_regular_borel_measurable hm hr (closed_borel_set hC)) hFinite hp.
  rewrite hZImage in hLower.
  exists K; split=>//; split=>//.
  apply:le_trans hLower _; apply:(@measure_mono R Y mu hm).
  rewrite (pruned_projection_limit_compact_fiber (measure_pruning_recursion hp) hZ).
  move=>y [[z a] [hz [_ ha]] <-]; exists (h a).
  + by exists a.
  + exact:esym hz.
Qed.
