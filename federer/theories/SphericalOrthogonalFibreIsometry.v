(** Federer (1969), 3.2.47, p. 283, last sentence:
    every actual Phi fibre is isometric with I. Left
    translation by a locally chosen orthogonal map proves the
    statement in the actual Hilbert Hom metric. All Hausdorff
    degrees, including degree zero, are retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct InnerProductUP InnerNorm InnerMetric
  OrthogonalMaps HomInner HomOrthogonalChange GammaNaturality
  EuclideanHomInnerCharts EuclideanHomCompositionBound EuclideanRectangularAdjoint
  EuclideanOrthogonalAdjointInverse UnitVectorOrthogonalMap
  SphericalOrthogonalProductAlgebra SphericalProductPreimageImage
  HausdorffMeasure HausdorffIsometricEmbedding.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_orthogonal_left_translation_distance]:
    left orthogonal translation preserves the actual Hilbert
    Hom distance, by 1.7.9, p. 35, supporting
    the fibre isometry of 3.2.47, p. 283. *)
Theorem euclidean_orthogonal_left_translation_distance (R:realType) n
    (t h g:Hom (R_n R n) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R n)
    (@euclidean_inner_product R n) (hom_as_linear t) ->
  inner_norm (@euclidean_hom_inner_productP R n n) (hom_comp t h-hom_comp t g)=
    inner_norm (@euclidean_hom_inner_productP R n n) (h-g).
Proof.
move=>ht.
have hDifference:hom_comp t h-hom_comp t g=
    Hom_sandwich (linear_id (R_n R n)) (hom_as_linear t) (h-g).
  apply:hom_ext=>x.
  change (t (h x)-t (g x)=t (h x-g x)).
  by rewrite linearB.
rewrite hDifference !euclidean_hilbert_hom_normE.
have hId:is_orthogonal_map (@euclidean_inner_product R n)
    (@euclidean_inner_product R n) (linear_id (R_n R n)) by move=>x y.
exact (@hom_norm_orthogonal_change R (R_n R n) (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) (@euclidean_inner_productP R n)
  n (@coordinate_basis R n) (@coordinate_basisP R n)
  (linear_id (R_n R n)) (hom_as_linear t) hId ht (h-g)).
Qed.

(** Source for [spherical_orthogonal_fibre_isometry_exists]:
    the actual whole fibre Phi inverse{z} is isometric
    with the actual original I, 3.2.47, p. 283.
    The orthogonal translation is an existential witness only. *)
Theorem spherical_orthogonal_fibre_isometry_exists (R:realType) n (c z:R_n R n.+1):
  inner_norm (@euclidean_inner_productP R n.+1) c= 1 ->
  inner_norm (@euclidean_inner_productP R n.+1) z= 1 ->
  exists (F G:Hom (R_n R n.+1) (R_n R n.+1)->Hom (R_n R n.+1) (R_n R n.+1)),
    cancel F G /\
    (forall x y,mdist (F x:inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1)) (F y)=
      mdist (x:inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1)) y) /\
    F @` spherical_orthogonal_isotropy c=spherical_orthogonal_preimage c [set z].
Proof.
move=>hc hz.
pose V:=R_n R n.+1.
pose H:=Hom V V.
have [t [ht hValue]]:=@unit_vector_orthogonal_map_exists R n.+1 c z (ltn0Sn n) hc hz.
pose T:Hom V V:=hom_of_linear t.
have hT:is_orthogonal_map (@euclidean_inner_product R n.+1)
    (@euclidean_inner_product R n.+1) (hom_as_linear T):=ht.
pose F:=fun h:H=>hom_comp T h.
pose G:=fun h:H=>hom_comp (euclidean_rectangular_adjoint T) h.
have hCancel:cancel F G.
  move=>h; apply:hom_ext=>x.
  change (euclidean_rectangular_adjoint T (T (h x))=h x).
  exact (@euclidean_orthogonal_adjoint_cancel R n.+1 T hT (h x)).
exists F,G; split; first exact hCancel.
split.
- move=>x y; rewrite !inner_metric_distanceE.
  exact (@euclidean_orthogonal_left_translation_distance R n.+1 T x y hT).
- apply/seteqP; split=>g.
  + move=>[h [hO hFixed] <-]; split.
    * move=>x y; change (euclidean_inner_product (T (h x)) (T (h y))=euclidean_inner_product x y).
      by rewrite hT hO.
    * change (T (h c)=z); by rewrite hFixed.
  + move=>[hg hgc]; exists (G g).
    * split.
      -- move=>x y; change (euclidean_inner_product
          (euclidean_rectangular_adjoint T (g x)) (euclidean_rectangular_adjoint T (g y))=
          euclidean_inner_product x y).
         by rewrite (euclidean_orthogonal_adjoint_orthogonal hT) hg.
      -- change (euclidean_rectangular_adjoint T (g c)=c).
         rewrite hgc -hValue; exact (@euclidean_orthogonal_adjoint_cancel R n.+1 T hT c).
    * apply:hom_ext=>x.
      change (T (euclidean_rectangular_adjoint T (g x))=g x).
      exact (@euclidean_orthogonal_adjoint_cancel_reverse R n.+1 T hT (g x)).
Qed.

(** Source for [spherical_orthogonal_fibre_measure]: the
    last sentence of 3.2.47, p. 283, preserves
    the actual Hausdorff outer measure of every whole fibre
    in every natural degree, by 2.10.11, p. 176. *)
Theorem spherical_orthogonal_fibre_measure (R:realType) n (c z:R_n R n.+1):
  inner_norm (@euclidean_inner_productP R n.+1) c= 1 ->
  inner_norm (@euclidean_inner_productP R n.+1) z= 1 ->forall q,
  @hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1)) q
    (spherical_orthogonal_preimage c [set z])=
  @hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1)) q
    (spherical_orthogonal_isotropy c).
Proof.
move=>hc hz q.
have [F [G [hCancel [hDistance hImage]]]]:=spherical_orthogonal_fibre_isometry_exists hc hz.
rewrite -hImage.
exact (@hausdorff_isometric_embedding_invariance R
  (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1))
  (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1)) F G hCancel hDistance q
  (spherical_orthogonal_isotropy c)).
Qed.
