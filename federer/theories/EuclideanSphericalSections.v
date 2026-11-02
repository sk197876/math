(** Federer (1969), 2.10.27, pp. 190–191: the Euclidean spherical
    upper-integral inequality. Natural section degree k and all coordinate
    dimensions, including empty blocks, are included. The proof follows the
    ball-cover argument using source-indexed sums and the sealed integral
    profile. The zero-dimensional Euclidean base is the project's unit-mass
    convention. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanLebesgueDimensions MetricCartesianProductUP
  EuclideanSphericalCutoff SphericalFamilyCutoffs HausdorffFibreCutoffs HausdorffMeasure
  HausdorffProductLowerBound MetricScaleEnvelope MeasureUP MeasureBasic PointMassMeasure
  ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic MeasureIntegralUP
  MeasureIntegralBounds MeasureIntegralUniqueness IncreasingUpperIntegralBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [zero_dimensional_spherical_section_integral]:
    supporting empty-product case of the second
    inequality in 2.10.27, pp. 190–191.
    Extend the printed Euclidean statement to R^0
    using unit mass at its sole vector. Every
    section has the same spherical mass as A,
    so the integral is exact for any degree. *)
Lemma zero_dimensional_spherical_section_integral (R : realType) k
    (A : set (inner_metric_space (@euclidean_inner_productP R 0))) :
  is_measure_integral (@euclidean_lebesgue_measure R 0)
    (partial_function_total (fun y=>(@spherical_measure R (inner_metric_space (@euclidean_inner_productP R 0)) k
      (metric_product_section (fun a b=>@euclidean_block_join R 0 0 (a,b)) A y) : extended_real_line R)))
    (@spherical_measure R (inner_metric_space (@euclidean_inner_productP R 0)) k A).
Proof.
have hsec y : metric_product_section (fun a b=>@euclidean_block_join R 0 0 (a,b)) A y=A.
  have he z : @euclidean_block_join R 0 0 (y,z)=z.
    by rewrite (@coordinate_zero R (euclidean_block_join (y,z))) (@coordinate_zero R z).
  apply/seteqP; split=> z hz.
  - change (A (euclidean_block_join (y,z))) in hz; by rewrite he in hz.
  - change (A (euclidean_block_join (y,z))); by rewrite he.
have hf : (fun y=>(@spherical_measure R (inner_metric_space (@euclidean_inner_productP R 0)) k
      (metric_product_section (fun a b=>@euclidean_block_join R 0 0 (a,b)) A y) : extended_real_line R))=
    (fun _ : inner_metric_space (@euclidean_inner_productP R 0)=>
      (@spherical_measure R (inner_metric_space (@euclidean_inner_productP R 0)) k A : extended_real_line R)).
  apply: funext=> y; by rewrite hsec.
rewrite hf.
have hi := @nonnegative_extended_constant_integral R (inner_metric_space (@euclidean_inner_productP R 0))
  (@euclidean_lebesgue_measure R 0) (@euclidean_lebesgue_is_measure R 0) _
  (measure_nonnegative (@spherical_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R 0)) k) A).
have hwhole : @euclidean_lebesgue_measure R 0 setT = 1 by exact (@point_mass_in R (inner_metric_space (@euclidean_inner_productP R 0)) 0%R setT Logic.I).
by rewrite hwhole mule1 in hi.
Qed.

(** Source for [federer_2_10_27_spherical]: direct second
    inequality in 2.10.27, pp. 190–191, for
    Euclidean coordinate blocks, with sharp constant
    one. All natural degrees and empty blocks are
    included; no measurability or finite-mass
    premise is imposed on A or its sections.
    The continuous real-degree extension remains
    outside the present natural-degree interface. *)
Theorem federer_2_10_27_spherical (R : realType) m n k
    (A : set (inner_metric_space (@euclidean_inner_productP R (m+n)))) :
  measure_upper_integral (@euclidean_lebesgue_measure R m)
    (partial_function_total (fun y=>(@spherical_measure R (inner_metric_space (@euclidean_inner_productP R n)) k
      (metric_product_section (fun a b=>@euclidean_block_join R m n (a,b)) A y) : extended_real_line R)))<=
    @spherical_measure R (inner_metric_space (@euclidean_inner_productP R (m+n))) (k+m) A.
Proof.
case: (posnP (m+n))=> [hzero|hdim].
- have hboth : (m+n==0)%N by apply/eqP.
  move: hboth; rewrite addn_eq0=> /andP [/eqP hm /eqP hn].
  move: A; rewrite hm hn=> A.
  have hi := @zero_dimensional_spherical_section_integral R k A.
  have he := measure_upper_integral_unique (measure_upper_integral_specification _ _) hi.2.1.
  have hk : (k+0)%N=k by rewrite addn0.
  by rewrite he hk.
- have hnonneg := measure_nonnegative
    (@spherical_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R (m+n))) (k+m)) A.
  case hM : (@spherical_measure R (inner_metric_space (@euclidean_inner_productP R (m+n))) (k+m) A)
      => [M| |] in hnonneg *; [|exact: leey|by []].
  apply: (@nonnegative_upper_integral_increasing_bound R
    (inner_metric_space (@euclidean_inner_productP R m)) (@euclidean_lebesgue_measure R m)
    (@euclidean_lebesgue_is_measure R m)
    (spherical_set_family_cutoff (fun y=>metric_product_section (fun a b=>@euclidean_block_join R m n (a,b)) A y) k)
    (fun y=>(@spherical_measure R (inner_metric_space (@euclidean_inner_productP R n)) k
      (metric_product_section (fun a b=>@euclidean_block_join R m n (a,b)) A y) : extended_real_line R)) M).
  + exact: spherical_set_family_cutoff_nonnegative.
  + exact: spherical_set_family_cutoffs_increasing.
  + exact: spherical_set_family_cutoffs_supremum.
  + move=> j; apply: (@euclidean_spherical_cutoff_integral_bound R m n k A
      ((j.+1%:R : R)^-1)%R M _ hdim _ (metric_scale_envelope_specification _ _ _) _).
    * by rewrite invr_gt0 ltr0n.
    * by rewrite hM.
Qed.
