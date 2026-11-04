(** Federer (1969), 3.2.47, p. 283: the
    reduction by 3.2.29 can use class-one manifolds
    contained in the original sphere. Actual common smooth
    sphere charts, compactness and the finite core argument
    discharge that containment for every original finite rectifiable E. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  UnitSphereSpace FiniteInnerSmoothSubmanifoldUP SphericalUnitSphereSmooth
  CompactSubmanifoldRectifiableContainedCover RectifiableManifoldCoverUP RectifiableSetUP HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_rectifiable_class_one_cover]: the
    actual sphere-contained class-one cover underlying the
    3.2.29 appeal in 3.2.47, p. 283.
    All natural r and positive ambient dimensions remain;
    neither E measurability nor a chosen atlas is assumed. *)
Theorem spherical_rectifiable_class_one_cover (R:realType) n r (E:set (R_n R n.+1)):
  E `<=` @euclidean_unit_sphere_set R n.+1 ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n.+1)) r) r E ->
  exists C:set (set (R_n R n.+1)),is_countable_submanifold_measure_cover r 1%N E C /\
    (forall M,C M ->M `<=` @euclidean_unit_sphere_set R n.+1).
Proof.
move=>hES hRect.
have hS:=inner_smooth_submanifold_class (@spherical_unit_sphere_smooth R n.+1) 1%N.
have hDegree:(n.+1-1=n)%N by rewrite subn1 succnK.
rewrite hDegree in hS.
exact (@compact_submanifold_rectifiable_contained_cover R n.+1 n r
  (@euclidean_unit_sphere_set R n.+1) E hS (@euclidean_unit_sphere_compact R n.+1) hES hRect).
Qed.
