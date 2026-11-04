(** Federer (1969), 3.2.48, p. 284: the actual
    Hausdorff group measure is translation invariant. The original
    carrier and ambient Hilbert Hom metric occur on both sides;
    actual left orthogonal translations give whole-set isometries. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets functions constructive_ereal topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric EuclideanHomInnerCharts OrthogonalMaps OrthogonalGroupTopology
  OrthogonalGroupHaarMeasure EuclideanOrthogonalInvariantMeasures
  LinearGroupTopology LinearGroupSealed IsotropyGroupTopology TopologicalGroupUP TopologicalGroupLaws
  SphericalOrthogonalFibreIsometry OrthogonalGroupHausdorffCarrier
  HausdorffMeasure HausdorffIsometricEmbedding MeasurePushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [orthogonal_group_hausdorff_left_invariant]: the
    left Haar invariance of actual H^nu on O(N)
    asserted in 3.2.48, p. 284. The stronger
    isometry argument applies to every Hausdorff degree and
    arbitrary, possibly nonmeasurable group subsets. *)
Theorem orthogonal_group_hausdorff_left_invariant (R:realType) N
    (mulS:euclidean_orthogonal_group R N->euclidean_orthogonal_group R N->euclidean_orthogonal_group R N)
    (invS:euclidean_orthogonal_group R N->euclidean_orthogonal_group R N)
    (eS:euclidean_orthogonal_group R N):
  is_subgroup_restriction
    (linear_group_mul (@euclidean_inner_productP R N) (@coordinate_basisP R N))
    (linear_group_inv (@euclidean_inner_productP R N) (@coordinate_basisP R N))
    (linear_group_unit (@euclidean_inner_productP R N) (@coordinate_basisP R N))
    (euclidean_orthogonal_group R N) mulS invS eS ->forall q g,
  measure_pushforward (mulS g) (@orthogonal_group_hausdorff_measure R N q)=
    @orthogonal_group_hausdorff_measure R N q.
Proof.
move=>hS q g; apply:funext=>A.
pose O:=euclidean_orthogonal_group R N.
pose V:=R_n R N.
pose H:=inner_metric_space (@euclidean_hom_inner_productP R N N).
pose om:=@orthogonal_element_map R V (@euclidean_inner_product R N)
  (@euclidean_inner_productP R N) N (@coordinate_basis R N) (@coordinate_basisP R N).
pose F:=fun w:H=>hom_comp (om (invS g)) w.
pose G:=fun w:H=>hom_comp (om g) w.
have hInv:=orthogonal_element_inv hS g.
have hGroup:=topological_group_laws (lch_group_topological (orthogonal_group_lch hS)).
have hCancel:cancel F G.
  move=>w; apply:hom_ext=>x; exact (hInv.2 (w x)).
have hDistance (x y:H):@mdist R H (F x) (F y)=mdist x y.
  rewrite !inner_metric_distanceE.
  exact (@euclidean_orthogonal_left_translation_distance R N (om (invS g)) x y
    (orthogonal_element_orthogonal (invS g))).
have hImage:om @` ((mulS g) @^-1` A)=F @` (om @` A).
  apply/seteqP; split=>w.
  - move=>[h hA <-]; exists (om (mulS g h)); first by exists (mulS g h).
    apply:hom_ext=>x.
    rewrite /F /om (orthogonal_element_mul hS) !hom_compE.
    exact (hInv.1 (om h x)).
  - move=>[z [h hA <-] <-]; exists (mulS (invS g) h).
    + change (A (mulS g (mulS (invS g) h))).
      by rewrite (group_mulKVg hGroup).
    + exact (orthogonal_element_mul hS (invS g) h).
rewrite /measure_pushforward /orthogonal_group_hausdorff_measure -/om hImage.
exact (@hausdorff_isometric_embedding_invariance R H H F G hCancel hDistance q (om @` A)).
Qed.
