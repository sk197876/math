(** Federer (1969), 4.1.2, p. 347: a Borel exceptional
    set whose every parallel line slice is null is itself null.
    Fubini is applied to (x,t) |-> x+t v, then the original
    translation invariance recovers the source measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormMetricContinuity NormMetricScaleContinuity
  TopologicalProductMaps GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext EuclideanLineProductBorel
  RealMetricBackground LebesgueScalarMeasure TopologicalBorel BorelFunctionBasic
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureAlmostPositiveWitness
  PartialFunctionUP PartialFunctionBasic MeasureIntegralUP MeasureIntegralUniqueness MeasureConullZeroIntegral
  ProductMeasure ProductSections ProductSetFubini ProductNullFubini
  CountablyMeasurableUP CountablyMeasurableProduct CountablyMeasurableSubsets MeasurePushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section EuclideanDirectionalNullSlices.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hN).
Local Notation RT := (real_line_metric R).
Local Notation mu := (@euclidean_lebesgue_measure R n).
Local Notation beta := (@lebesgue_scalar_measure R).
Local Notation hm := (euclidean_lebesgue_is_measure R n).
Local Notation hb := (lebesgue_scalar_is_measure R).
Variable v:X.
Variable A:set X.

(** Source for [euclidean_directional_null_slices]: the
    actual Fubini transfer behind the reflexive locally Lipschitz
    clause of Federer 4.1.2, p. 347. The direction may be zero;
    the conclusion uses the original Euclidean outer measure. *)
Theorem euclidean_directional_null_slices:
  @borel_set XT A ->
  (forall x:X,beta [set t:R|A (x+t*:v)]=0%E) ->
  mu A=0%E.
Proof.
move=>hA hSlices.
pose S:set (XT*RT):=[set p|A (p.1+p.2*:v)].
have hScale:continuous (fun p:XT*RT=>(p.2*:v:XT)).
  move=>p; exact:(continuous_comp (@second_projection_continuous XT RT p)
    (@real_norm_metric_scalar_orbit_continuous R X N hN v p.2)).
have hPair:=topological_pair_continuous (@first_projection_continuous XT RT) hScale.
have hMap:continuous (fun p:XT*RT=>(p.1+p.2*:v:XT)).
  move=>p; exact:(continuous_comp (hPair p)
    (@real_norm_metric_add_continuous R X N hN (p.1,p.2*:v))).
have hSBorel:@borel_set (XT*RT)%type S.
  exact:(borel_function_preimage (continuous_borel_function hMap) hA).
have hSMeas:=@euclidean_line_product_borel_measurable R n S hSBorel.
have hWhole:=@product_whole_countably_measurable R X R mu beta hm hb
  (euclidean_lebesgue_countably_measurable R n) (lebesgue_scalar_countably_measurable R).
have hSCount:=measurable_subset_countably_measurable
  (product_measure_is_measure hm hb) hSMeas (subsetT S) hWhole.
have[_ [_ [hIntegral _]]]:=@product_set_fubini R X R mu beta hm hb S hSCount.
have hZeroIntegral:is_measure_integral mu
    (partial_function_total (fun x=>beta (product_vertical_section S x))) 0%E.
  apply:(@measure_almost_zero_integral R X mu hm _).
  apply:(@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm)).
  move=>x _; change (beta [set t:R|A (x+t*:v)]=0%E).
  exact:hSlices x.
have hZero:product_measure hm hb S=0%E:=measure_integral_unique hIntegral hZeroIntegral.
have hHorizontal:=@product_null_horizontal_sections R X R mu beta hm hb S hZero.
pose J:set RT:=`[(0:R),(1:R)].
have hPositive:(0<beta J)%E.
  by rewrite /J lebesgue_scalar_segment ?ler01 // subr0 lte_fin ltr01.
have hNonzero:beta J<>0%E.
  move=>h; by rewrite h ltxx in hPositive.
have[t [_ ht]]:=@measure_almost_positive_set_witness R R beta hb
  J [set t|mu (product_horizontal_section S t)=0%E] hNonzero hHorizontal.
have hTranslation:=congr1 (fun nu=>nu A) (@euclidean_distribution_measure_translation R n (t*:v)).
change (mu [set x:X|A (x+t*:v)]=mu A) in hTranslation.
change (mu [set x:X|A (x+t*:v)]=0%E) in ht.
by rewrite -hTranslation.
Qed.
End EuclideanDirectionalNullSlices.
