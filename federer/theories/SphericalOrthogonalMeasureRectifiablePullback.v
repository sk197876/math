(** Federer (1969), 3.2.47(3), p. 283: the
    local product argument also gives finite-mass rectifiability
    of the preimage of a finite rectifiable Borel base.
    This discharges finiteness when applying coarea to a
    genuine Borel measure hull of an arbitrary original set. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp finmap classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanHomInnerCharts SphericalBasePointBasis SphericalFiniteBaseCores
  SphericalCompactPatchMeasureRectifiable SphericalProductPreimageImage
  UnitSphereSpace MetricClosedBalls RectifiableSetUP MeasureRectifiableSubset
  MeasureRectifiableFiniteUnions HausdorffMeasure MeasureUP TopologicalBorel BorelFamilyBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_orthogonal_measure_rectifiable_pullback]:
    finite rectifiable Borel base sets have finite rectifiable
    whole preimages, supporting the application of 3.2.22(3)
    in 3.2.47(3), p. 283. Finitely many fixed
    compact base cores retain the whole original isotropy. *)
Theorem spherical_orthogonal_measure_rectifiable_pullback (R:realType) n
    (c:R_n R n.+1) (E:set (R_n R n.+1)) r:
  inner_norm (@euclidean_inner_productP R n.+1) c= 1 ->
  E `<=` @euclidean_unit_sphere_set R n.+1 ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n.+1)) r) r E ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R n.+1)) E ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1)) (r+n*(n-1)%/2))
    (r+n*(n-1)%/2)%N (spherical_orthogonal_preimage c E).
Proof.
move=>hc hES hRect hBorel.
have [e [he [hON hFirst]]]:=@spherical_base_point_basis_exists R n c hc.
have [F [hF hCover]]:=@spherical_finite_base_cores R n e he hON.
pose V:=R_n R n.+1.
pose H:=Hom V V.
pose X:=inner_metric_space (@euclidean_inner_productP R n.+1).
pose Y:=inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1).
pose J:=(H*(V*R))%type.
pose K:=fun p:J=>(@euclidean_unit_sphere_set R n.+1 `&`
  @metric_closed_ball R X p.2.1 p.2.2).
have hUnion:spherical_orthogonal_preimage c E=
    \bigcup_(p:F) spherical_orthogonal_preimage c (E `&` K (val p)).
  apply/seteqP; split=>g.
  - move=>[hg hE]; have [p hp hgp]:=hCover (g c) (hES _ hE).
    exists ([` hp]%fset); first exact I.
    exact (conj hg (conj hE hgp)).
  - move=>[p _ [hg [hE _]]]; exact (conj hg hE).
rewrite hUnion.
refine (@measure_rectifiable_finite_union R Y [the finType of (F:Type)]
  (@hausdorff_measure R Y (r+n*(n-1)%/2)%N) (r+n*(n-1)%/2)%N
  (fun p:F=>spherical_orthogonal_preimage c (E `&` K (val p)))
  (@hausdorff_measure_is_measure R Y (r+n*(n-1)%/2)%N) _).
move=>p.
have [ht [hK hPatch]]:=hF (val p) (valP p).
have hSubset:E `&` K (val p) `<=` K (val p) by move=>a ha; exact ha.2.
have hLocal:=@spherical_compact_patch_measure_rectifiable R n e he hON (val p).1
  (K (val p)) (E `&` K (val p)) r ht hK hPatch hSubset.
rewrite hFirst in hLocal; apply:hLocal.
- exact (@measure_rectifiable_subset R X (@hausdorff_measure R X r) r E (E `&` K (val p))
    (fun a ha=>ha.1) hRect).
- apply:(borel_family_binary_intersection (borel_sets_family X) hBorel _).
  apply:closed_borel_set.
  exact (compact_closed (@metric_hausdorff R X) hK).
Qed.
