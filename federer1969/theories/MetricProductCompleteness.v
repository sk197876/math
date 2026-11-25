(** General topology supporting Federer (1969), 2.2.10, p. 65: the product
    of complete metric spaces is complete. A proper Cauchy filter has Cauchy
    projections; their limits give the product limit. This elementary proof
    uses the abstract completeness laws, not an external
    product-completeness theorem. Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import CompleteMetricUP MetricProductBackground MetricCauchyImages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [complete_metric_product]: supporting completeness
    assertion for X times N in Federer 2.2.10, p. 65,
    stated for two arbitrary complete metric factors. Neither
    factor is required to be inhabited. *)
Theorem complete_metric_product (R : realType) (T U : metricType R) :
  is_complete_metric_space T -> is_complete_metric_space U ->
  is_complete_metric_space [the metricType R of metric_product T U].
Proof.
move=> hT hU F PF hc.
have PF1 : ProperFilter (@fst T U @ F) := @fmap_proper_filter _ _ (@fst T U) F PF.
have PF2 : ProperFilter (@snd T U @ F) := @fmap_proper_filter _ _ (@snd T U) F PF.
have hc1 : cauchy (@fst T U @ F).
  apply: (@distance_nonincreasing_cauchy_image R [the metricType R of metric_product T U] T (@fst T U) F PF)=> // x y.
  by rewrite metric_product_distanceE le_max lexx.
have hc2 : cauchy (@snd T U @ F).
  apply: (@distance_nonincreasing_cauchy_image R [the metricType R of metric_product T U] U (@snd T U) F PF)=> // x y.
  by rewrite metric_product_distanceE le_max lexx orbT.
have [x hx] := hT _ PF1 hc1; have [y hy] := hU _ PF2 hc2.
have FF : Filter F := @filter_filter _ F PF.
exists (x,y)=> W [[A B] [hA hB] hW].
apply: (@filterS _ F FF _ _ _ (@filterI _ F FF _ _ (hx A hA) (hy B hB))).
move=> p [ha hb]; apply: hW; by split.
Qed.
