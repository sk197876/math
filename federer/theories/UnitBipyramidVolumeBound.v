(** Federer (1969), 2.10.36, printed p. 198: the centred two-apex convex
    hull has volume at least height times base volume divided by ambient
    dimension. Prove the normalised half-height-one case from the actual
    horizontal-section Fubini identity and the integrated hat profile. The
    enclosing convex set is measurable; the base needs only finite outer
    volume. Neither compactness nor base measurability is needed for this
    supporting comparison. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanCoordinateSplit InnerConvex AffineDilation
  EuclideanLebesgueDimensions EuclideanBipyramidSections EuclideanHeadSectionIntegral
  ProjectedVolumeDilation BipyramidHatIntegral ProductSections LebesgueScalarMeasure
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic PartialFunctionUP PartialFunctionBasic
  PartialExtendedOrderLoci MeasureIntegralUP MeasureIntegralComparison SummableRealFunctionUP SummableRealArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [unit_bipyramid_volume_lower_bound]: supporting
    normalised two-apex volume estimate in
    the last display of 2.10.36,
    p. 198. The half-height is
    one; the coefficient is 2/(n+1).
    Infinite volume of the enclosing set
    and natural base dimension zero are allowed. *)
Theorem unit_bipyramid_volume_lower_bound (R : realType) (n : nat)
    (K : set (inner_metric_space (@euclidean_inner_productP R n)))
    (C : set (inner_metric_space (@euclidean_inner_productP R n.+1)))
    (z : inner_metric_space (@euclidean_inner_productP R n)) :
  is_inner_convex C -> measure_measurable (@euclidean_lebesgue_measure R n.+1) C ->
  (euclidean_lebesgue_measure n K< +oo)%E ->
  (forall x, K x -> C (euclidean_join (x,0))) ->
  C (euclidean_join (z,1)) -> C (euclidean_join (z,-1)) ->
  (((2*n.+1%:R^-1)%R%:E)*euclidean_lebesgue_measure n K<=euclidean_lebesgue_measure n.+1 C)%E.
Proof.
move=> hconv hC hK hbase hplus hminus.
have hfin : euclidean_lebesgue_measure n K \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative (euclidean_lebesgue_is_measure R n) K)); exact hK.
pose a := fine (euclidean_lebesgue_measure n K).
have hval : euclidean_lebesgue_measure n K=a%:E by rewrite /a fineK.
pose w (t : R) := if `|t|<=1 then (1-`|t|)^+n else 0.
pose G (t : R) := euclidean_lebesgue_measure n
  (product_horizontal_section ((@euclidean_join R n) @^-1` C) t).
have hp := @bipyramid_hat_profile_integral R n.
have hs := @real_total_integral_scale R R (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) w (2*n.+1%:R^-1) a hp.
have hG := @euclidean_head_section_integral R n C hC.
have hbound t : ((a*w t)%:E<=G t)%E.
  rewrite /w; case: ifP=> ht; last by rewrite mulr0; exact: (measure_nonnegative (euclidean_lebesgue_is_measure R n)).
  have hinc := @convex_unit_bipyramid_section_inclusion R n K C z hconv hbase hplus hminus t ht.
  have hh := measure_mono (euclidean_lebesgue_is_measure R n) hinc.
  have hr : 0<=1-`|t| by rewrite subr_ge0.
  rewrite euclidean_affine_dilation_volume (ger0_norm hr) hval -EFinM mulrC in hh.
  exact hh.
have hae : measure_almost_everywhere (@lebesgue_scalar_measure R)
    (partial_extended_le_locus (real_total_integrand (fun t=>a*w t)) (partial_function_total G)).
  apply: (@measure_almost_everywhere_mono R R (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R)
    setT _ _ (measure_almost_everywhere_true (lebesgue_scalar_is_measure R)))=> t _.
  exists (a*w t)%:E,(G t); split; first by apply/real_total_integrand_graph.
  split; first reflexivity; exact: hbound.
have hh := measure_integral_monotone (lebesgue_scalar_is_measure R) hs hG hae.
by rewrite hval -EFinM mulrC.
Qed.
