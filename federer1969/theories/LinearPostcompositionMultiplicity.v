(** Supporting the affine normal-coordinate calculation in Federer (1969),
    2.10.16, p. 178. Postcomposing a map with a linear endomorphism K of R^m
    multiplies its Lebesgue multiplicity integral by the absolute
    determinant. Use 2.7.16, p. 134, which explicitly treats both invertible
    K and the null image of singular K; no generic transversality or
    almost-everywhere rank hypothesis is needed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanLebesgueHaar EuclideanLinearMaps EuclideanLebesgueDeterminant
  TensorUP CompleteMetricUP BorelImageMeasurability TopologicalBorel BorelRegularMeasureUP
  MappingMultiplicity MappingMultiplicityLaws BorelMultiplicityIntegral BorelImageCoverCost
  BorelCaratheodoryMeasure BijectionPostcompositionMultiplicity ExtendedRealOrderTopology
  PartialFunctionBasic MeasureUP MeasureBasic MeasureIntegralUP MeasureAlmostUP MeasureAlmostBasic
  MeasureConullZeroIntegral MeasurableFunctionUP MeasurePushforward MeasureScaleIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [linear_postcomposition_multiplicity_integral]:
    supporting determinant change for 2.10.16, p. 178,
    from the actual linear-image law of 2.7.16, pp. 134–135.
    Singular K contributes zero because every nonempty fibre
    lies over its null image, even if the base integral is
    infinite. The invertible case uses the inverse pushforward. *)
Theorem linear_postcomposition_multiplicity_integral (R : realType)
    (X : metricType R) (m : nat) (f : X -> inner_metric_space (@euclidean_inner_productP R m))
    (K : {linear R_n R m -> R_n R m}) (A : set X) J :
  is_complete_metric_space X -> (exists D : set X, countable D /\ dense D) ->
  continuous f -> borel_set A ->
  is_measure_integral (@euclidean_lebesgue_measure R m)
    (partial_function_total (fun y => (@mapping_multiplicity R X _ f A y : extended_real_line R))) J ->
  is_measure_integral (@euclidean_lebesgue_measure R m)
    (partial_function_total (fun y => (@mapping_multiplicity R X _ (fun x => K (f x)) A y : extended_real_line R)))
    ((`|euclidean_det K|)%R%:E*J).
Proof.
move=> hX hsep hf hA hi.
pose Y := [the metricType R of inner_metric_space (@euclidean_inner_productP R m)].
pose Leb := @euclidean_lebesgue_measure R m.
have hm := @euclidean_lebesgue_is_measure R m.
case: (eqVneq (euclidean_det K) 0%R)=> [hzero|hne].
- rewrite hzero normr0 mul0e.
  have hz : Leb ((K : Y -> Y) @` setT)=0.
    have he := @euclidean_lebesgue_linear_image R m K setT.
    rewrite hzero normr0 mul0e in he; exact he.
  have hconull : measure_almost_everywhere Leb (~` ((K : Y -> Y) @` setT)).
    by rewrite /measure_almost_everywhere setCK hz.
  apply: (measure_almost_zero_integral hm).
  apply: (@measure_almost_everywhere_mono R Y Leb hm _ _ _ hconull)=> y hy.
  change (@mapping_multiplicity R X Y (fun x => K (f x)) A y=0).
  apply ((@mapping_multiplicity_zero_iff R X Y (fun x => K (f x)) A y).2).
  move=> [x hx he]; apply: hy; by exists (f x).
- have hinj := (euclidean_det_injective K).1 hne.
  have [G [hKG hGK]] := euclidean_linear_inverse hinj.
  have hdet := euclidean_det_inverse hKG.
  have hGne : euclidean_det G!=0%R.
    apply/eqP=> hG; move: hdet; rewrite hG mul0r=> /eqP.
    by rewrite eq_sym oner_eq0.
  have hnorm : (`|euclidean_det G|*`|euclidean_det K|= 1)%R.
    by move: (congr1 (fun t : R => (`|t|)%R) hdet); rewrite /= normrM normr1.
  have hGnorm : (`|euclidean_det G|!=0)%R by rewrite normr_eq0.
  have hinv : (`|euclidean_det G|^-1=`|euclidean_det K|)%R.
    have h := congr1 (fun t => (`|euclidean_det G|^-1*t)%R) hnorm.
    rewrite /= mulrA (mulVf hGnorm) mul1r mulr1 in h.
    exact: esym h.
  have hp : measure_pushforward (G : Y -> Y) Leb=measure_scale `|euclidean_det K| Leb.
    apply/funext=> S; rewrite /measure_pushforward /measure_scale.
    have hg := @euclidean_lebesgue_linear_pushforward R m G hGne S.
    rewrite hinv in hg; exact hg.
  have hc : continuous (fun x : X => (K (f x) : Y)).
    move=> x; exact (continuous_comp (hf x) (@euclidean_linear_continuous R m K (f x))).
  have [D [hD hden]] := hsep.
  have hmeas : is_measure_measurable_function Leb
      (partial_function_total (fun y => (@mapping_multiplicity R X Y (fun x => K (f x)) A y : extended_real_line R))).
    have hImage S : borel_set S -> measure_measurable Leb ((fun x => K (f x)) @` S).
      apply: (@continuous_borel_image_measurable R X Y (fun x => K (f x)) Leb hm S hX
        (ex_intro _ D (conj hD hden)) (@metric_hausdorff R Y) hc).
      move=> C hC; exact (@borel_regular_borel_measurable R Y Leb hm
        (@euclidean_lebesgue_borel_regular R m) C (closed_borel_set hC)).
    exact (@borel_multiplicity_integral R X Y (fun x => K (f x)) Leb hm D A hD hden hImage hA).1.
  have hpos : (0<`|euclidean_det K|)%R by rewrite normr_gt0.
  exact (@bijective_postcomposition_multiplicity_integral R X Y Y f K G Leb Leb hm hm A
    `|euclidean_det K| J hKG hGK hpos hp hi hmeas).
Qed.
