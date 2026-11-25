(** Federer (1969), 3.2.47(1),(2), p. 283: both
    original arbitrary-source pullback assertions. The actual
    finite compact base cover and smooth product charts discharge
    the local product argument. All natural degrees and positive
    ambient dimensions, including the two-atom line sphere, remain. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  finmap classical_sets cardinality constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNormalization InnerNorm InnerMetric OrthogonalMaps
  LinearBasis OrthonormalFamilies EuclideanHomInnerCharts SphericalBasePointBasis
  UnitSphereSpace MetricClosedBalls SphericalFiniteBaseCores
  SphericalProductPreimageImage SphericalCompactPatchPullback
  RectifiableSetUP RectifiableElementary CompactSubmanifoldRectifiable
  HausdorffMeasure MeasureUP MeasureBasic MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_orthogonal_pullback_rectifiable_null]:
    both actual original-set conclusions of 3.2.47(1),(2),
    p. 283, without a Borel or finite-mass premise.
    The finite-family argument retains genuine rectifiability,
    rather than replacing it by a countable almost-cover. *)
Theorem spherical_orthogonal_pullback_rectifiable_null (R:realType) n
    (c:R_n R n.+1) (E:set (R_n R n.+1)) r:
  inner_norm (@euclidean_inner_productP R n.+1) c= 1 ->
  E `<=` @euclidean_unit_sphere_set R n.+1 ->
  (@is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n.+1)) r E ->
    @is_m_rectifiable R (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1))
      (r+n*(n-1)%/2)%N (spherical_orthogonal_preimage c E)) /\
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n.+1)) r E=0%E ->
    @hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1))
      (r+n*(n-1)%/2)%N (spherical_orthogonal_preimage c E)=0%E).
Proof.
move=>hc hES.
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
    \bigcup_(p in [set` F]) spherical_orthogonal_preimage c (E `&` K p).
  apply/seteqP; split=>g.
  - move=>[hg hEg]; have [p hp hgp]:=hCover (g c) (hES _ hEg).
    exists p; first exact hp; split; first exact hg.
    by split.
  - move=>[p hp [hg [hEg _]]]; by split.
have hLocal p (hp:p \in F):
    (@is_m_rectifiable R X r (E `&` K p) ->
      @is_m_rectifiable R Y (r+n*(n-1)%/2)%N
        (spherical_orthogonal_preimage c (E `&` K p))) /\
    (@hausdorff_measure R X r (E `&` K p)=0%E ->
      @hausdorff_measure R Y (r+n*(n-1)%/2)%N
        (spherical_orthogonal_preimage c (E `&` K p))=0%E).
  have [ht [hK hPatch]]:=hF p hp.
  have hSubset:E `&` K p `<=` K p by move=>a ha; exact ha.2.
  have hResult:=@spherical_compact_patch_pullback R n e he hON p.1
    (K p) (E `&` K p) r ht hK hPatch hSubset.
  by rewrite hFirst in hResult.
split.
- move=>hE; rewrite hUnion.
  apply:(@rectifiable_finite_indexed_union R Y (r+n*(n-1)%/2)%N
    [the choiceType of J] [set` F]
    (fun p=>spherical_orthogonal_preimage c (E `&` K p)) (finite_fset F)).
  move=>p hp; apply:(hLocal p hp).1.
  exact:(@rectifiable_subset R X r E (E `&` K p) (fun a ha=>ha.1) hE).
- move=>hE; rewrite hUnion.
  apply:(@measure_null_countable_union R Y [the choiceType of J]
    (@hausdorff_measure R Y (r+n*(n-1)%/2)%N)
    (@hausdorff_measure_is_measure R Y (r+n*(n-1)%/2)%N)
    [set` F] (fun p=>spherical_orthogonal_preimage c (E `&` K p))
    (finite_set_countable (finite_fset F))).
  move=>p hp; apply:(hLocal p hp).2.
  exact (@measure_null_subset R X (@hausdorff_measure R X r)
    (@hausdorff_measure_is_measure R X r) (E `&` K p) E (fun a ha=>ha.1) hE).
Qed.

(** Source for [federer_3_2_47_1]: the first printed
    assertion of 3.2.47, p. 283: genuine r
    rectifiability of E implies genuine r plus mu rectifiability
    of its whole original orthogonal-group preimage. *)
Theorem federer_3_2_47_1 (R:realType) n (c:R_n R n.+1) (E:set (R_n R n.+1)) r:
  inner_norm (@euclidean_inner_productP R n.+1) c= 1 ->
  E `<=` @euclidean_unit_sphere_set R n.+1 ->
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n.+1)) r E ->
  @is_m_rectifiable R (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1))
    (r+n*(n-1)%/2)%N (spherical_orthogonal_preimage c E).
Proof. move=>hc hE; exact:(@spherical_orthogonal_pullback_rectifiable_null R n c E r hc hE).1. Qed.

(** Source for [federer_3_2_47_2]: the second printed
    assertion of 3.2.47, p. 283: an arbitrary
    Hausdorff r null original set has Hausdorff r plus mu
    null whole preimage. No source rectifiability is assumed. *)
Theorem federer_3_2_47_2 (R:realType) n (c:R_n R n.+1) (E:set (R_n R n.+1)) r:
  inner_norm (@euclidean_inner_productP R n.+1) c= 1 ->
  E `<=` @euclidean_unit_sphere_set R n.+1 ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n.+1)) r E=0%E ->
  @hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1))
    (r+n*(n-1)%/2)%N (spherical_orthogonal_preimage c E)=0%E.
Proof. move=>hc hE; exact:(@spherical_orthogonal_pullback_rectifiable_null R n c E r hc hE).2. Qed.
