(** Federer (1969), 3.2.34, p. 271: the
    restricted coarea fibres agree with the whole
    original distance levels for radii in (a,b)
    and are empty at all other radii. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanOneCoordinate
  MappingMultiplicity HausdorffMeasure MeasureUP MeasureBasic PartialFunctionUP PartialFunctionBasic
  PartialFunctionPrecomposition PartialZeroExtension RealOpenIntervals ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_distance_level_strip_fibre]:
    the equality of the coarea fibre with f^-1{y}
    at radii a<y<b in Federer 3.2.34,
    p. 271. It concerns the whole original
    level set, with no boundedness or finite-mass
    premise on the source or on individual fibres. *)
Lemma euclidean_distance_level_strip_fibre (R:realType) n (d:R_n R n->R) a b y:
  real_open_interval a b (euclidean_one_project y) ->
  mapping_fibre (fun z=>euclidean_one_embed (d z)) [set x|a<d x<b] y=
    [set x|d x=euclidean_one_project y].
Proof.
move=>[hay hyb]; apply/seteqP; split=>x.
- move=>[_ he]; have hh:=congr1 (@euclidean_one_project R) he.
  by rewrite euclidean_one_embedK in hh.
- move=>he; split.
  + by apply/andP; split; rewrite he.
  + by rewrite he euclidean_one_projectK.
Qed.

(** Source for [euclidean_distance_outside_strip_fibre]:
    the fibre vanishes outside the scalar integration
    interval in Federer 3.2.34, p. 271,
    including both endpoints. *)
Lemma euclidean_distance_outside_strip_fibre (R:realType) n (d:R_n R n->R) a b y:
  ~real_open_interval a b (euclidean_one_project y) ->
  mapping_fibre (fun z=>euclidean_one_embed (d z)) [set x|a<d x<b] y=set0.
Proof.
move=>hOutside; apply/seteqP; split; last by move=>x [].
move=>x [/andP[hax hxb] he]; exfalso; apply:hOutside.
have hScalar:=congr1 (@euclidean_one_project R) he.
rewrite euclidean_one_embedK in hScalar.
by rewrite -hScalar; split.
Qed.

(** Source for [euclidean_distance_level_cutoff_graph]:
    the scalar integral in Federer 3.2.34, p. 271,
    is the zero extension on (a,b) of the
    mass of the whole original level set. The
    graph equation retains empty fibres and infinite
    mass exactly, before any integral is chosen. *)
Lemma euclidean_distance_level_cutoff_graph (R:realType) n (d:R_n R n->R) a b y z:
  partial_function_graph
    (partial_function_total (fun y=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) (n-1)
      (mapping_fibre (fun x=>euclidean_one_embed (d x)) [set x|a<d x<b] y)
      :extended_real_line R))) y z <->
  partial_function_graph
    (partial_function_precompose (@euclidean_one_project R)
      (partial_function_zero_extension (0%E:extended_real_line R)
        (real_open_interval a b) (partial_function_total (fun t:R=>
          (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n))
            (n-1) [set x|d x=t]:extended_real_line R))))) y z.
Proof.
change (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n))
  (n-1) (mapping_fibre (fun x=>euclidean_one_embed (d x)) [set x|a<d x<b] y)=z <->partial_function_graph
  (partial_function_zero_extension (0%E:extended_real_line R)
    (real_open_interval a b) (partial_function_total (fun t:R=>
      (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n))
        (n-1) [set x|d x=t]:extended_real_line R)))) (euclidean_one_project y) z).
rewrite partial_function_zero_extension_graph.
change ((@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n))
  (n-1) (mapping_fibre (fun x=>euclidean_one_embed (d x)) [set x|a<d x<b] y)=z) <->
  (real_open_interval a b (euclidean_one_project y) /\
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) (n-1)
      [set x|d x=euclidean_one_project y]=z) \/
  (~real_open_interval a b (euclidean_one_project y) /\z=0%E)).
case:(pselect (real_open_interval a b (euclidean_one_project y)))=>hy.
- rewrite (euclidean_distance_level_strip_fibre d hy); split=>hz.
  + left; by split.
  + case:hz=>[[_ hz]|[hn _]]; first exact hz; exfalso; exact:hn hy.
- rewrite (euclidean_distance_outside_strip_fibre d hy)
    (measure_empty (@hausdorff_measure_is_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) (n-1))).
  split=>hz.
  + right; split=>//; exact:esym hz.
  + case:hz=>[[hn _]|[_ hz]]; first by exfalso; exact:hy hn.
    exact:esym hz.
Qed.
