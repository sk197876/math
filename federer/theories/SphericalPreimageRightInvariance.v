(** Federer (1969), 3.2.48, p. 286: right multiplication by
    members of the actual isotropy preserves the metric, Phi, and every
    Hausdorff restriction to the original preimage. Outer-measure identities
    hold on all test subsets, without Borel assumptions. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanHomInnerCharts EuclideanRectangularAdjoint EuclideanOrthogonalAdjointInverse OrthogonalMaps
  HomCompositionDeterminant OrthogonalKinematicIsometries SphericalProductPreimageImage
  HausdorffMeasure HausdorffIsometryMeasurability MeasureRestriction MeasurePushforward InjectiveRestrictionPushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_hom_right_translation_inverse]: actual
    inverse laws for the metric-preserving right action used in
    3.2.48, p. 286. They hold on the full ambient Hom space. *)
Lemma euclidean_hom_right_translation_inverse (R:realType) N
    (h:Hom (R_n R N) (R_n R N)):
  is_orthogonal_map (@euclidean_inner_product R N) (@euclidean_inner_product R N) (hom_as_linear h) ->
  cancel (fun g:Hom (R_n R N) (R_n R N)=>hom_comp g h) (fun g:Hom (R_n R N) (R_n R N)=>hom_comp g (euclidean_rectangular_adjoint h)) /\
  cancel (fun g:Hom (R_n R N) (R_n R N)=>hom_comp g (euclidean_rectangular_adjoint h)) (fun g:Hom (R_n R N) (R_n R N)=>hom_comp g h).
Proof.
move=>hh; split=>g; apply:hom_ext=>v.
- change (g (h (euclidean_rectangular_adjoint h v))=g v).
  by rewrite (euclidean_orthogonal_adjoint_cancel_reverse hh).
- change (g (euclidean_rectangular_adjoint h (h v))=g v).
  by rewrite (euclidean_orthogonal_adjoint_cancel hh).
Qed.

(** Source for [euclidean_hom_right_translation_distance]: metric
    invariance under the actual right isotropy action, 3.2.48, p. 286,
    derived from Hilbert Hom invariance in 1.7.9, p. 35. *)
Lemma euclidean_hom_right_translation_distance (R:realType) N
    (h:Hom (R_n R N) (R_n R N)):
  is_orthogonal_map (@euclidean_inner_product R N) (@euclidean_inner_product R N) (hom_as_linear h) ->
  forall x y,mdist (hom_comp x h:inner_metric_space (@euclidean_hom_inner_productP R N N)) (hom_comp y h)=
    mdist (x:inner_metric_space (@euclidean_hom_inner_productP R N N)) y.
Proof.
move=>hh x y.
pose H:=Hom (R_n R N) (R_n R N).
pose idV:H:=hom_of_linear (linear_id (R_n R N)).
pose F:Hom H H:=hom_of_linear (@hom_right_composition R (R_n R N) (R_n R N) h).
have hId:is_orthogonal_map (@euclidean_inner_product R N) (@euclidean_inner_product R N) (hom_as_linear idV) by move=>u v.
have hNorm z:inner_norm (@euclidean_hom_inner_productP R N N) (F z)=
    inner_norm (@euclidean_hom_inner_productP R N N) z.
  have hSame:hom_comp idV (hom_comp z h)=F z by apply:hom_ext=>u.
  have hValue:=@orthogonal_kinematic_sandwich_norm R N h idV z hh hId.
  by rewrite hSame in hValue.
rewrite !inner_metric_distanceE.
change (inner_norm (@euclidean_hom_inner_productP R N N) (F x-F y)=
  inner_norm (@euclidean_hom_inner_productP R N N) (x-y)).
by rewrite -linearB hNorm.
Qed.

(** Source for [spherical_preimage_right_translation_image]: the exact
    original preimage is invariant under the right isotropy action,
    3.2.48, p. 286. Original non-Borel subsets are retained. *)
Lemma spherical_preimage_right_translation_image (R:realType) N (c:R_n R N)
    (h:Hom (R_n R N) (R_n R N)) (E:set (R_n R N)):
  is_orthogonal_map (@euclidean_inner_product R N) (@euclidean_inner_product R N) (hom_as_linear h) ->h c=c ->
  (fun g:Hom (R_n R N) (R_n R N)=>hom_comp g h) @` spherical_orthogonal_preimage c E=spherical_orthogonal_preimage c E.
Proof.
move=>hh hc.
have hInvC:euclidean_rectangular_adjoint h c=c.
  have hFixed:=congr1 (euclidean_rectangular_adjoint h) hc.
  rewrite (euclidean_orthogonal_adjoint_cancel hh) in hFixed; exact (esym hFixed).
have [hLeft hRight]:=euclidean_hom_right_translation_inverse hh.
apply/seteqP; split=>g.
- move=>[w [hw hwE] <-]; split.
  + move=>u v; change (euclidean_inner_product (w (h u)) (w (h v))=euclidean_inner_product u v).
    by rewrite hw hh.
  + change (E (w (h c))); by rewrite hc.
- move=>[hg hgE]; exists (hom_comp g (euclidean_rectangular_adjoint h)).
  + split.
    * move=>u v; change (euclidean_inner_product
        (g (euclidean_rectangular_adjoint h u)) (g (euclidean_rectangular_adjoint h v))=euclidean_inner_product u v).
      by rewrite hg (euclidean_orthogonal_adjoint_orthogonal hh).
    * change (E (g (euclidean_rectangular_adjoint h c))); by rewrite hInvC.
  + exact (hRight g).
Qed.

(** Source for [spherical_preimage_right_translation_measure]: the
    original completed source Hausdorff restriction is invariant under
    every actual right stabilizer action in 3.2.48, p. 286. Full
    outer-measure equality handles arbitrary test sets and completions. *)
Theorem spherical_preimage_right_translation_measure (R:realType) N (c:R_n R N)
    (h:Hom (R_n R N) (R_n R N)) (E:set (R_n R N)) q:
  is_orthogonal_map (@euclidean_inner_product R N) (@euclidean_inner_product R N) (hom_as_linear h) ->h c=c ->
  measure_pushforward (fun g:Hom (R_n R N) (R_n R N)=>hom_comp g h)
    (measure_restrict (@hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R N N)) q)
      (spherical_orthogonal_preimage c E))=
  measure_restrict (@hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R N N)) q)
    (spherical_orthogonal_preimage c E).
Proof.
move=>hh hc.
have [hLeft hRight]:=euclidean_hom_right_translation_inverse hh.
rewrite (injective_restriction_pushforward _ _ (can_inj hLeft))
  (@hausdorff_bijective_isometry_pushforward R
    (inner_metric_space (@euclidean_hom_inner_productP R N N))
    (inner_metric_space (@euclidean_hom_inner_productP R N N))
    (fun g:Hom (R_n R N) (R_n R N)=>hom_comp g h) (fun g:Hom (R_n R N) (R_n R N)=>hom_comp g (euclidean_rectangular_adjoint h)) hLeft hRight
    (euclidean_hom_right_translation_distance hh) q)
  (spherical_preimage_right_translation_image E hh hc).
reflexivity.
Qed.
