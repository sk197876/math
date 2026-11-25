(** Federer (1969), 3.2.48, p. 286: the right stabilizer action
    on the second factor of the original source product is an actual
    isometry and preserves its Hausdorff restriction. The joint family
    is continuous in the specified Cartesian Hilbert metric. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanHomInnerCharts OrthogonalMaps EuclideanRectangularAdjoint EuclideanOrthogonalAdjointInverse
  HomCompositionDeterminant ProductInner ProductInnerNormBounds CartesianTopExteriorNorm
  OrthogonalKinematicIsometries SphericalPreimageRightInvariance SphericalProductPreimageImage
  HausdorffMeasure HausdorffIsometryMeasurability MeasureRestriction MeasurePushforward InjectiveRestrictionPushforward
  EuclideanOrthogonalInvariantMeasures OrthogonalGroupTopology OrthogonalGroupHaarMeasure HomSpaceTopology
  SphericalIsotropyTransverseAction SphericalIsotropyActionContinuity InnerCartesianContinuousMaps TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [orthogonal_cartesian_right_translation]: the actual
    map (x,y) to (x,y h) in the source-invariance step of 3.2.48,
    p. 286. No restriction or representative of the source is selected. *)
Definition orthogonal_cartesian_right_translation (R:realType) N
    (h:Hom (R_n R N) (R_n R N))
    (z:Hom (R_n R N) (R_n R N)*Hom (R_n R N) (R_n R N)):=
  (z.1,hom_comp z.2 h).

(** Source for [orthogonal_cartesian_right_translation_inverse]:
    exact inverse laws of the original source action, 3.2.48, p. 286,
    before any measure or completed-measurability transport is used. *)
Lemma orthogonal_cartesian_right_translation_inverse (R:realType) N
    (h:Hom (R_n R N) (R_n R N)):
  is_orthogonal_map (@euclidean_inner_product R N) (@euclidean_inner_product R N) (hom_as_linear h) ->
  cancel (orthogonal_cartesian_right_translation h)
    (orthogonal_cartesian_right_translation (euclidean_rectangular_adjoint h)) /\
  cancel (orthogonal_cartesian_right_translation (euclidean_rectangular_adjoint h))
    (orthogonal_cartesian_right_translation h).
Proof.
move=>hh; have [hLeft hRight]:=euclidean_hom_right_translation_inverse hh.
split.
- move=>[x y]; by rewrite /orthogonal_cartesian_right_translation /= hLeft.
- move=>[x y]; by rewrite /orthogonal_cartesian_right_translation /= hRight.
Qed.

(** Source for [orthogonal_cartesian_right_translation_distance]: the
    original source metric is invariant under the actual right action,
    3.2.48, p. 286. Both Cartesian factor inner products are retained. *)
Lemma orthogonal_cartesian_right_translation_distance (R:realType) N
    (h:Hom (R_n R N) (R_n R N)):
  is_orthogonal_map (@euclidean_inner_product R N) (@euclidean_inner_product R N) (hom_as_linear h) ->
  let P:=inner_metric_space (product_inner_productP
    (@euclidean_hom_inner_productP R N N) (@euclidean_hom_inner_productP R N N)) in
  forall x y,mdist (orthogonal_cartesian_right_translation h x:P) (orthogonal_cartesian_right_translation h y)=mdist (x:P) y.
Proof.
move=>hh P.
pose H:=Hom (R_n R N) (R_n R N).
pose hH:=@euclidean_hom_inner_productP R N N.
pose idV:H:=hom_of_linear (linear_id (R_n R N)).
pose idH:Hom H H:=hom_of_linear (linear_id H).
pose C:Hom H H:=hom_of_linear (@hom_right_composition R (R_n R N) (R_n R N) h).
pose F:=cartesian_linear_hom idH C.
have hId:is_orthogonal_map (@euclidean_inner_product R N) (@euclidean_inner_product R N) (hom_as_linear idV) by move=>u v.
have hC u v:euclidean_hom_inner_product (C u) (C v)=euclidean_hom_inner_product u v.
  have hLeft z:hom_comp idV z=z by apply:hom_ext=>w.
  have hValue:=@orthogonal_kinematic_sandwich_pairing R N h idV u v hh hId.
  by rewrite !hLeft in hValue.
have hF z:F z=orthogonal_cartesian_right_translation h z.
  case:z=>x y; by rewrite /F cartesian_linear_homE.
have hOrth:is_orthogonal_map (product_inner hH hH) (product_inner hH hH) (hom_as_linear F).
  move=>x y.
  change (product_inner hH hH (F x) (F y)=product_inner hH hH x y).
  rewrite !hF /orthogonal_cartesian_right_translation !product_innerE.
  change (euclidean_hom_inner_product x.1 y.1+euclidean_hom_inner_product (C x.2) (C y.2)=
    euclidean_hom_inner_product x.1 y.1+euclidean_hom_inner_product x.2 y.2).
  by rewrite hC.
move=>x y; rewrite !inner_metric_distanceE -!hF.
change (inner_norm (product_inner_productP hH hH) (F x-F y)=
  inner_norm (product_inner_productP hH hH) (x-y)).
by rewrite -linearB (orthogonal_map_norm (product_inner_productP hH hH)
  (product_inner_productP hH hH) hOrth).
Qed.

(** Source for [orthogonal_cartesian_right_translation_measure]: the
    exact source Hausdorff restriction is unchanged by the actual right
    isotropy action, 3.2.48, p. 286. Arbitrary original source subsets
    and all natural Hausdorff grades are retained. *)
Theorem orthogonal_cartesian_right_translation_measure (R:realType) N (c:R_n R N)
    (h:Hom (R_n R N) (R_n R N)) (A B:set (R_n R N)) q:
  is_orthogonal_map (@euclidean_inner_product R N) (@euclidean_inner_product R N) (hom_as_linear h) ->h c=c ->
  let P:=inner_metric_space (product_inner_productP
    (@euclidean_hom_inner_productP R N N) (@euclidean_hom_inner_productP R N N)) in
  measure_pushforward (orthogonal_cartesian_right_translation h)
    (measure_restrict (@hausdorff_measure R P q)
      [set z:Hom (R_n R N) (R_n R N)*Hom (R_n R N) (R_n R N)|
        spherical_orthogonal_preimage c A z.1 /\spherical_orthogonal_preimage c B z.2])=
  measure_restrict (@hausdorff_measure R P q)
    [set z:Hom (R_n R N) (R_n R N)*Hom (R_n R N) (R_n R N)|
      spherical_orthogonal_preimage c A z.1 /\spherical_orthogonal_preimage c B z.2].
Proof.
move=>hh hc P.
have [hLeft hRight]:=orthogonal_cartesian_right_translation_inverse hh.
have hB:=spherical_preimage_right_translation_image B hh hc.
pose S:=[set z:Hom (R_n R N) (R_n R N)*Hom (R_n R N) (R_n R N)|
  spherical_orthogonal_preimage c A z.1 /\spherical_orthogonal_preimage c B z.2].
have hImage:orthogonal_cartesian_right_translation h @` S=S.
  apply/seteqP; split=>z.
  - move=>[w [hwA hwB] <-]; split; first exact hwA.
    rewrite -hB; exists w.2; first exact hwB; reflexivity.
  - move=>[hzA hzB].
    rewrite -hB in hzB; have [w hw hValue]:=hzB.
    exists (z.1,w); first by split.
    rewrite /orthogonal_cartesian_right_translation /= hValue.
    exact (esym (surjective_pairing z)).
rewrite (injective_restriction_pushforward _ _ (can_inj hLeft))
  (@hausdorff_bijective_isometry_pushforward R P P (orthogonal_cartesian_right_translation h)
    (orthogonal_cartesian_right_translation (euclidean_rectangular_adjoint h)) hLeft hRight
    (orthogonal_cartesian_right_translation_distance hh) q) hImage.
reflexivity.
Qed.

(** Source for [orthogonal_cartesian_right_inverse_action_continuous]:
    joint continuity for the exact original source product action in
    3.2.48, p. 286. The actual inner-metric coordinate projections,
    continuous stabilizer action and actual Cartesian pair prove it. *)
Theorem orthogonal_cartesian_right_inverse_action_continuous (R:realType) d
    (Q:Hom (R_n R (1+d)) (R_n R (1+d))):
  is_orthogonal_map (@euclidean_inner_product R (1+d))
    (@euclidean_inner_product R (1+d)) (hom_as_linear Q) ->
  let P:=inner_metric_space (product_inner_productP
    (@euclidean_hom_inner_productP R (1+d) (1+d)) (@euclidean_hom_inner_productP R (1+d) (1+d))) in
  continuous (fun z:euclidean_orthogonal_group R d*P=>
    (orthogonal_cartesian_right_translation
      (euclidean_rectangular_adjoint (spherical_isotropy_transverse_operator Q (orthogonal_element_map z.1))) z.2:P)).
Proof.
move=>hQ P.
pose H0:=Hom (R_n R (1+d)) (R_n R (1+d)).
pose hH:=@euclidean_hom_inner_productP R (1+d) (1+d).
pose H:=inner_metric_space hH.
pose G:=euclidean_orthogonal_group R d.
have [hFirst hSecond]:=@inner_cartesian_projections_continuous R H0 H0 _ _ hH hH.
have hLeft:continuous (fun z:G*P=>(z.2.1:H)).
  move=>z; exact (continuous_comp (@second_projection_continuous G P z) (hFirst z.2)).
have hPair:continuous (fun z:G*P=>(z.1,z.2.2):G*H).
  apply:topological_pair_continuous; first exact:first_projection_continuous.
  move=>z; exact (continuous_comp (@second_projection_continuous G P z) (hSecond z.2)).
have hAction:=spherical_isotropy_right_inverse_action_continuous hQ.
have hRight:continuous (fun z:G*P=>(hom_comp z.2.2 (euclidean_rectangular_adjoint
    (spherical_isotropy_transverse_operator Q (orthogonal_element_map z.1))):H)).
  move=>z; exact (continuous_comp (hPair z) (hAction (z.1,z.2.2))).
exact (@inner_cartesian_pair_continuous R (G*P)%type H0 H0 _ _ hH hH
  (fun z=>z.2.1) (fun z=>hom_comp z.2.2 (euclidean_rectangular_adjoint
    (spherical_isotropy_transverse_operator Q (orthogonal_element_map z.1)))) hLeft hRight).
Qed.
