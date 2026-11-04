(** Federer (1969), 3.2.47(3), p. 283: the
    full r=0 mass conclusion under its original finite
    rectifiability premise on the whole preimage. The proved
    converse gives finite counting mass of E, hence E
    is actually finite and the exact whole-fibre sum applies. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets cardinality constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric EuclideanHomInnerCharts SphericalOrthogonalProductAlgebra
  SphericalProductPreimageImage SphericalOrthogonalConverseRectifiability
  SphericalFiniteBaseMass UnitSphereSpace RectifiableSetUP HausdorffMeasure
  HausdorffCountingMeasure CountingMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [spherical_orthogonal_pullback_mass_zero_degree]:
    the exact zero-degree case of 3.2.47(3), p. 283,
    with only the original actual preimage rectifiability premise.
    The empty set and every positive counting atom remain. *)
Theorem spherical_orthogonal_pullback_mass_zero_degree (R:realType) n
    (c:R_n R n.+1) (E:set (R_n R n.+1)):
  inner_norm (@euclidean_inner_productP R n.+1) c= 1%R ->
  E `<=` @euclidean_unit_sphere_set R n.+1 ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1)) (n*(n-1)%/2))
    (n*(n-1)%/2)%N (spherical_orthogonal_preimage c E) ->
  @hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1))
    (n*(n-1)%/2)%N (spherical_orthogonal_preimage c E)=
  @hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1))
    (n*(n-1)%/2)%N (spherical_orthogonal_isotropy c)*
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n.+1)) 0 E.
Proof.
move=>hc hES hPreimage.
have hTarget:=@spherical_orthogonal_converse_rectifiability R n c E 0 hc hES hPreimage.
have hFinite:finite_set E.
  apply:contrapT=>hNot.
  have hInfinite:@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n.+1)) 0 E=+oo.
    rewrite hausdorff_zero_counting_measure.
    exact (@counting_measure_infinite R
      (inner_metric_space (@euclidean_inner_productP R n.+1)) E hNot).
  have hMass:=hTarget.2; by rewrite hInfinite ltxx in hMass.
exact (@spherical_finite_base_mass R n c E hc hES hFinite).
Qed.
