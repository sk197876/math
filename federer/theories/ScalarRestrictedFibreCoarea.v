(** Federer (1969), 3.2.36, p. 273: scalar transport of actual
    restricted distance coarea, retaining exact whole fibres in the cutoff. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanOneCoordinate
  EuclideanLebesgueDimensions ScalarEuclideanApproximateLimits LebesgueScalarMeasure RealOpenIntervals
  MappingMultiplicity HausdorffMeasure MeasureUP MeasureBasic MeasurePushforward MeasureIntegralUP
  MeasureSubsetIntegral MeasureIntegralGraphEquivalence InjectivePushforwardIntegral
  PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition PartialZeroExtension ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [restricted_scalar_fibre_cutoff_graph]: scalar identification
    of the fibre integral in Federer 3.2.36, p. 273. Intersecting
    the source strip with an arbitrary set T preserves its entire
    intersection with each interior level. At every other radius the
    restricted fibre is empty; no mass or measurability premise is needed. *)
Lemma restricted_scalar_fibre_cutoff_graph (R:realType) n k (f:R_n R n->R)
    (T:set (R_n R n)) a b y z:
  partial_function_graph (partial_function_total (fun y=>(@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) k
    (mapping_fibre (fun x=>euclidean_one_embed (f x)) ([set x|a<f x<b] `&` T) y)
      :extended_real_line R))) y z <->
  partial_function_graph (partial_function_precompose (@euclidean_one_project R)
    (partial_function_zero_extension (0%E:extended_real_line R) (real_open_interval a b)
      (partial_function_total (fun s:R=>(@hausdorff_measure R
        (inner_metric_space (@euclidean_inner_productP R n)) k
        [set x|f x=s /\T x]:extended_real_line R))))) y z.
Proof.
pose s:=euclidean_one_project y.
pose F:=mapping_fibre (fun x=>euclidean_one_embed (f x)) ([set x|a<f x<b] `&` T) y.
change (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) k F=z <->
  partial_function_graph (partial_function_zero_extension (0%E:extended_real_line R)
    (real_open_interval a b) (partial_function_total (fun s:R=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) k [set x|f x=s /\T x]
        :extended_real_line R)))) s z).
rewrite partial_function_zero_extension_graph.
case:(pselect (real_open_interval a b s))=>hs.
- have hF:F=[set x|f x=s /\T x].
    apply/seteqP; split=>x.
    + move=>[[_ hx] he]; split=>//.
      have h:=congr1 (@euclidean_one_project R) he; by rewrite euclidean_one_embedK in h.
    + move=>[he hx]; split; last by rewrite he /s euclidean_one_projectK.
      split; last exact hx.
      change (a<f x<b); rewrite he; apply/andP; exact hs.
  rewrite hF; split=>hz.
  + left; by split.
  + case:hz=>[[_ hz]|[hn _]]=>//; exfalso; exact:hn hs.
- have hF:F=set0.
    apply/seteqP; split; last by move=>x [].
    move=>x [[/andP[hax hxb] _] he]; exfalso; apply:hs.
    have h:=congr1 (@euclidean_one_project R) he; rewrite euclidean_one_embedK in h.
    by rewrite /s -h; split.
  rewrite hF (measure_empty (@hausdorff_measure_is_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) k)).
  split=>hz.
  + right; split=>//; exact:esym hz.
  + case:hz=>[[hn _]|[_ hz]]; first by exfalso; exact:hs hn.
    exact:esym hz.
Qed.

(** Source for [restricted_scalar_fibre_integral]: the scalar-radius
    version of the first coarea equality in Federer 3.2.36, p. 273.
    The existing scalar identification with R^1 transports the actual
    integral, with all original fibres and infinite values retained. *)
Lemma restricted_scalar_fibre_integral (R:realType) n k (f:R_n R n->R)
    (T:set (R_n R n)) a b c:
  is_measure_integral (@euclidean_lebesgue_measure R 1)
    (partial_function_total (fun y=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) k
      (mapping_fibre (fun x=>euclidean_one_embed (f x)) ([set x|a<f x<b] `&` T) y)
        :extended_real_line R))) c ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) (real_open_interval a b)
    (partial_function_total (fun s:R=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) k [set x|f x=s /\T x]
        :extended_real_line R))) c.
Proof.
move=>hI.
have hPre:=measure_integral_graph_equivalent
  (@restricted_scalar_fibre_cutoff_graph R n k f T a b) hI.
have hPush:measure_pushforward (@euclidean_one_project R) (@euclidean_lebesgue_measure R 1)=
    @lebesgue_scalar_measure R.
  apply:funext=>A; exact:Logic.eq_sym (euclidean_one_project_measure_preimage A).
have hi:=(@injective_pushforward_integral_iff R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R 1)] R
  (@euclidean_lebesgue_measure R 1) (euclidean_lebesgue_is_measure R 1)
  (@euclidean_one_project R) _ (can_inj (@euclidean_one_projectK R)) _).1 hPre.
by rewrite hPush in hi.
Qed.
