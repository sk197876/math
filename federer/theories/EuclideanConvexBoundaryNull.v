(** Federer (1969), 3.2.35, p. 272:
    boundaries of nonempty bounded open convex
    bodies have zero ambient Lebesgue measure.
    This includes the zero-dimensional projected
    target, whose boundary is empty. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  InnerConvex CoveringFamilyUP EuclideanOpenConvexBoundary RectifiableFiniteHausdorffMass
  HausdorffDimensionDrop EuclideanHausdorffLebesgue EuclideanLebesgueDimensions MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_open_convex_boundary_null]:
    the displayed ambient nullity of Bdry p(S)
    in Federer 3.2.35, p. 272. Genuine
    finite boundary rectifiability gives finite
    lower-degree Hausdorff mass, and 2.10.2(1)
    and 2.10.35 give zero ambient volume. In
    dimension zero nonemptiness makes the body
    the whole single-point space, with empty
    boundary; no negative degree is introduced. *)
Theorem euclidean_open_convex_boundary_null (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  S!=set0 ->open S ->is_inner_convex S ->metric_set_bounded S ->
  euclidean_lebesgue_measure n (closure S `\` interior S)=0%E.
Proof.
case:n S=>[S|n S] hNonempty hOpen hConvex hBound.
- have [a ha]:=hNonempty.
  have hWhole:S=setT.
    apply/seteqP; split=>x hx; first exact Logic.I.
    have hxa:x=a by rewrite (coordinate_zero x) (coordinate_zero a).
    by rewrite hxa.
  rewrite hWhole closureT interiorT setDv; exact:measure_empty (euclidean_lebesgue_is_measure R 0).
- have hRect:=@euclidean_open_convex_boundary_rectifiable R n.+1 S hNonempty hOpen hConvex hBound.
  rewrite subn1 in hRect.
  have hFinite:=@rectifiable_finite_hausdorff_mass R n n.+1 _ hRect.
  have hNull:=@hausdorff_finite_mass_higher_degree_zero R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n.+1)] n n.+1
    (closure S `\` interior S) (ltnSn n) hFinite.
  by rewrite (euclidean_hausdorff_spherical_lebesgue _).1 in hNull.
Qed.
