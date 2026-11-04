(** Federer (1969), 3.2.47(3), p. 283: the full
    first conclusion, finite Hausdorff rectifiability of the
    original E from finite Hausdorff rectifiability of its
    whole actual orthogonal-group preimage. Finitely many actual
    compact base cores reduce to the proved slicing argument. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  finmap classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric EuclideanHomInnerCharts SphericalBasePointBasis
  SphericalFiniteBaseCores SphericalCompactPatchConverse SphericalProductPreimageImage
  UnitSphereSpace MetricClosedBalls RectifiableSetUP MeasureRectifiableSubset
  MeasureRectifiableFiniteUnions HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_orthogonal_converse_rectifiability]:
    the first conclusion of 3.2.47(3), p. 283,
    for every natural r and arbitrary original E. Neither
    source measurability, target measurability nor a null
    hull excess is assumed. The slicing map and positive
    actual fibre mass are proved in the local argument. *)
Theorem spherical_orthogonal_converse_rectifiability (R:realType) n
    (c:R_n R n.+1) (E:set (R_n R n.+1)) r:
  inner_norm (@euclidean_inner_productP R n.+1) c= 1 ->
  E `<=` @euclidean_unit_sphere_set R n.+1 ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1)) (r+n*(n-1)%/2))
    (r+n*(n-1)%/2)%N (spherical_orthogonal_preimage c E) ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n.+1)) r) r E.
Proof.
move=>hc hES hRect.
have [e [he [hON hFirst]]]:=@spherical_base_point_basis_exists R n c hc.
have [F [hF hCover]]:=@spherical_finite_base_cores R n e he hON.
pose V:=R_n R n.+1.
pose H:=Hom V V.
pose X:=inner_metric_space (@euclidean_inner_productP R n.+1).
pose Y:=inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1).
pose J:=(H*(V*R))%type.
pose K:=fun p:J=>(@euclidean_unit_sphere_set R n.+1 `&`
  @metric_closed_ball R X p.2.1 p.2.2).
have hUnion:E=\bigcup_(p:F) (E `&` K (val p)).
  apply/seteqP; split=>a.
  - move=>ha; have [p hp haK]:=hCover a (hES a ha).
    exists ([` hp]%fset); by split.
  - by move=>[p _ [ha _]].
rewrite hUnion.
refine (@measure_rectifiable_finite_union R X [the finType of (F:Type)]
  (@hausdorff_measure R X r) r (fun p:F=>E `&` K (val p))
  (@hausdorff_measure_is_measure R X r) _).
move=>p.
have [ht [hK hPatch]]:=hF (val p) (valP p).
have hSubset:E `&` K (val p) `<=` K (val p) by move=>a ha; exact ha.2.
have hLocal:=@spherical_compact_patch_converse R n e he hON (val p).1
  (K (val p)) (E `&` K (val p)) r ht hK hPatch hSubset.
rewrite hFirst in hLocal.
apply:hLocal.
apply:(@measure_rectifiable_subset R Y (@hausdorff_measure R Y (r+n*(n-1)%/2)%N)
  (r+n*(n-1)%/2)%N (spherical_orthogonal_preimage c E)
  (spherical_orthogonal_preimage c (E `&` K (val p))) _ hRect).
move=>g hg; split; first exact hg.1.
exact hg.2.1.
Qed.
