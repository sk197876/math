(** Federer (1969), 3.2.48, p. 285: the original source
    restricted to a Borel member of each manifold partition is
    completed measurable and finitely rectifiable. The second original
    factor retains genuine rectifiability under restriction. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanHomInnerCharts ProductInner UnitSphereSpace SphericalProductPreimageImage SphericalKinematicSource
  RectifiableSetUP MeasureRectifiableSubset RectifiableElementary HausdorffMeasure
  HausdorffClosedCoverAgreement BorelRegularMeasureUP TopologicalBorel MeasureUP MeasureFiniteClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_kinematic_measurable_piece]: the inherited
    source hypotheses on each partition product in 3.2.48, p. 285.
    The original A and B need only be completed measurable; the
    partition members are Borel. No finite-mass or product-measurability
    premise is added to the application. *)
Theorem spherical_kinematic_measurable_piece (R:realType) d k m (c:R_n R (1+d))
    (A B E F:set (R_n R (1+d))):
  inner_norm (@euclidean_inner_productP R (1+d)) c= 1 ->
  A `<=` @euclidean_unit_sphere_set R (1+d) ->B `<=` @euclidean_unit_sphere_set R (1+d) ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (1+d))) k) k A ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (1+d))) k) A ->
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R (1+d))) m B ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (1+d))) m) B ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R (1+d))) E ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R (1+d))) F ->
  let P:=inner_metric_space (product_inner_productP
    (@euclidean_hom_inner_productP R (1+d) (1+d)) (@euclidean_hom_inner_productP R (1+d) (1+d))) in
  let S:=[set z:Hom (R_n R (1+d)) (R_n R (1+d))*Hom (R_n R (1+d)) (R_n R (1+d))|
    spherical_orthogonal_preimage c (A `&` E) z.1 /\spherical_orthogonal_preimage c (B `&` F) z.2] in
  is_measure_m_rectifiable (@hausdorff_measure R P ((k+d*(d-1)%/2)+(m+d*(d-1)%/2)))
    ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))%N S /\
  measure_measurable (@hausdorff_measure R P ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))) S.
Proof.
move=>hc hA hB hRA hMA hRB hMB hE hF P S.
pose X:=inner_metric_space (@euclidean_inner_productP R (1+d)).
have hAE:A `&` E `<=` A by move=>x hx; exact hx.1.
have hBF:B `&` F `<=` B by move=>x hx; exact hx.1.
have hRAE:=@measure_rectifiable_subset R X (@hausdorff_measure R X k) k A (A `&` E) hAE hRA.
have hRBF:=@rectifiable_subset R X m B (B `&` F) hBF hRB.
have hMAE:measure_measurable (@hausdorff_measure R X k) (A `&` E).
  exact (measure_measurable_intersection (@hausdorff_measure_is_measure R X k) hMA
    (borel_regular_borel_measurable (@hausdorff_measure_is_measure R X k)
      (@hausdorff_measure_borel_regular R X k) hE)).
have hMBF:measure_measurable (@hausdorff_measure R X m) (B `&` F).
  exact (measure_measurable_intersection (@hausdorff_measure_is_measure R X m) hMB
    (borel_regular_borel_measurable (@hausdorff_measure_is_measure R X m)
      (@hausdorff_measure_borel_regular R X m) hF)).
exact (@spherical_kinematic_source R d k m c (A `&` E) (B `&` F) hc
  (fun x hx=>hA x hx.1) (fun x hx=>hB x hx.1) hRAE hMAE hRBF hMBF).
Qed.
