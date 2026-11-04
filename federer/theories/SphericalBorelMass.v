(** Federer (1969), 3.2.47(3), p. 283: the
    exact mass identity for every original finite rectifiable
    Borel subset of the sphere. The actual sphere-contained
    class-one cover, disjoint Borel partition, null pullback
    and countable additivity complete the printed reduction. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanHomInnerCharts UnitSphereSpace SphericalOrthogonalProductAlgebra SphericalProductPreimageImage
  SphericalRectifiableManifoldCover SphericalSubmanifoldSubsetMass SphericalOrthogonalPreimageBorel
  SphericalOrthogonalPullback RectifiableManifoldCoverUP SubmanifoldBorel
  RectifiableSetUP MeasureRectifiableSubset HausdorffMeasure HausdorffClosedCoverAgreement
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureAlmostDisjointSum
  BorelRegularMeasureUP TopologicalBorel BorelFamilyBasic BorelPartition BorelSubordinatePartition
  NonnegativeSum NonnegativeSumSupport NonnegativeSumExtendedScale.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_borel_preimage_mass_balanced]: the
    original coarea mass equality of 3.2.47(3), p. 283,
    in balanced form for every finite rectifiable Borel E.
    All covering manifolds are proved to lie in Sphere;
    countable disjoint pieces retain the original E and
    whole fibres. No extra source-finiteness premise is needed. *)
Theorem spherical_borel_preimage_mass_balanced (R:realType) n r
    (c:R_n R n.+1) (E:set (R_n R n.+1)):
  inner_norm (@euclidean_inner_productP R n.+1) c= 1 ->
  E `<=` @euclidean_unit_sphere_set R n.+1 ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n.+1)) r) r E ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R n.+1)) E ->
  ((((Num.sqrt (2:R))^-1)^+r)%:E*
    @hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1))
      (r+n*(n-1)%/2)%N (spherical_orthogonal_preimage c E)=
    @hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1))
      (n*(n-1)%/2)%N (spherical_orthogonal_isotropy c)*
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n.+1)) r E)%E.
Proof.
move=>hc hES hRect hEB.
pose X:=inner_metric_space (@euclidean_inner_productP R n.+1).
pose Y:=inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1).
pose beta:=@hausdorff_measure R X r.
pose rho:=@hausdorff_measure R Y (r+n*(n-1)%/2)%N.
pose iota:=@hausdorff_measure R Y (n*(n-1)%/2)%N (spherical_orthogonal_isotropy c).
pose j:=(((Num.sqrt (2:R))^-1)^+r).
have hBeta:=@hausdorff_measure_is_measure R X r.
have hRho:=@hausdorff_measure_is_measure R Y (r+n*(n-1)%/2)%N.
have [C [hC hInside]]:=@spherical_rectifiable_class_one_cover R n r E hES hRect.
pose E0:=E `&` \bigcup_(M in C) M.
have hCB M (hM:C M):@borel_set X M.
  exact (euclidean_submanifold_borel (submanifold_measure_cover_class hC hM)).
have hE0B:@borel_set X E0.
  exact (borel_family_binary_intersection (borel_sets_family X) hEB
    (borel_set_countable_union (submanifold_measure_cover_countable hC) hCB)).
have hE0Null:beta (E `\` E0)=0%E.
  apply:(@measure_null_subset R X beta hBeta (E `\` E0)
    (E `\` \bigcup_(M in C) M) _ (submanifold_measure_cover_almost hC)).
  move=>x [hx hn]; split; first exact hx.
  by move=>hUnion; apply:hn; split.
have [P [hPartition hSub]]:=@borel_countable_cover_subordinate_partition X E0 C
  hE0B (submanifold_measure_cover_countable hC) hCB (fun x hx=>hx.2).
have hPE B (hB:P B):B `<=` E.
  move=>x hx; exact ((hSub B hB).1 x hx).1.
have hPB B (hB:P B):@borel_set X B:=borel_partition_members hPartition hB.
have hDisj B B' (hB:P B) (hB':P B') (hNe:B!=B') x (hx:B x) (hx':B' x):False.
  have hDifferent:B<>B'.
    by move=>hEqual; move:hNe; rewrite hEqual eqxx.
  have hEmpty:=borel_partition_disjoint hPartition hB hB' hDifferent.
  have hBoth:(B `&` B') x by split.
  by rewrite hEmpty in hBoth.
have hMeas B (hB:P B):measure_measurable beta B.
  exact (borel_regular_borel_measurable hBeta (@hausdorff_measure_borel_regular R X r) (@hPB B hB)).
have hBaseSum:beta E=nonnegative_sum P (fun B=>beta B).
  apply:(@measure_almost_disjoint_cover_sum R X [the choiceType of set X] beta hBeta E P id
    (borel_partition_countable hPartition) hPE hDisj hMeas).
  by rewrite (borel_partition_union hPartition).
have hLocal B (hB:P B):(j%:E*rho (spherical_orthogonal_preimage c B)=iota*beta B)%E.
  have [_ [M [hM hBM]]]:=hSub B hB.
  have hRectB:=@measure_rectifiable_subset R X beta r E B (@hPE B hB) hRect.
  exact (@spherical_submanifold_subset_mass R n r c M B hc
    (submanifold_measure_cover_class hC hM) (hInside M hM) hBM hRectB (@hPB B hB)).
have hSourceSub B (hB:P B):spherical_orthogonal_preimage c B `<=` spherical_orthogonal_preimage c E.
  move=>g hg; exact (conj hg.1 (@hPE B hB _ hg.2)).
have hSourceDisj B B' (hB:P B) (hB':P B') (hNe:B!=B') g
    (hg:spherical_orthogonal_preimage c B g) (hg':spherical_orthogonal_preimage c B' g):False.
  exact (@hDisj B B' hB hB' hNe (g c) hg.2 hg'.2).
have hSourceMeas B (hB:P B):measure_measurable rho (spherical_orthogonal_preimage c B).
  exact (borel_regular_borel_measurable hRho
    (@hausdorff_measure_borel_regular R Y (r+n*(n-1)%/2)%N)
    (@spherical_orthogonal_preimage_borel R n.+1 c B (@hPB B hB))).
have hPreRemainder:rho (spherical_orthogonal_preimage c E `\`
    \bigcup_(B in P) spherical_orthogonal_preimage c B)=0%E.
  have hNull:=@federer_3_2_47_2 R n c (E `\` E0) r hc
    (fun x hx=>hES x hx.1) hE0Null.
  apply:(@measure_null_subset R Y rho hRho _ (spherical_orthogonal_preimage c (E `\` E0)) _ hNull).
  move=>g [hg hn]; split; first exact hg.1.
  split; first exact hg.2.
  move=>hE0.
  have hUnion:(\bigcup_(B in P) B) (g c) by rewrite (borel_partition_union hPartition).
  have [B hB hBg]:=hUnion; apply:hn; exists B; first exact hB.
  exact (conj hg.1 hBg).
have hSourceSum:rho (spherical_orthogonal_preimage c E)=
    nonnegative_sum P (fun B=>rho (spherical_orthogonal_preimage c B)).
  exact (@measure_almost_disjoint_cover_sum R Y [the choiceType of set X] rho hRho
    (spherical_orthogonal_preimage c E) P (fun B=>spherical_orthogonal_preimage c B)
    (borel_partition_countable hPartition) hSourceSub hSourceDisj hSourceMeas hPreRemainder).
have hj:(0<=j)%R by apply:exprn_ge0; rewrite invr_ge0 sqrtr_ge0.
have hIota:(0<=iota)%E.
  exact (@measure_nonnegative R Y (@hausdorff_measure R Y (n*(n-1)%/2)%N)
    (@hausdorff_measure_is_measure R Y (n*(n-1)%/2)%N) _).
change (j%:E*rho (spherical_orthogonal_preimage c E)=iota*beta E)%E.
rewrite hSourceSum -(@nonnegative_sum_extended_scale R [the choiceType of set X] P
  (fun B=>rho (spherical_orthogonal_preimage c B)) j%:E ltac:(by rewrite lee_fin)
  (fun B _=>@measure_nonnegative R Y rho hRho _)).
have hSums:nonnegative_sum P (fun B=>(j%:E*rho (spherical_orthogonal_preimage c B))%E)=
    nonnegative_sum P (fun B=>(iota*beta B)%E).
  apply:nonnegative_sum_ext=>B hB; exact (@hLocal B hB).
rewrite hSums (@nonnegative_sum_extended_scale R [the choiceType of set X] P
  (fun B=>beta B) iota hIota (fun B _=>@measure_nonnegative R X beta hBeta _)) -hBaseSum.
reflexivity.
Qed.
