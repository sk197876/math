(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1),(5), pp. 326, 328:
    the original Q_j is the opaque image of the actual
    prefix germ homomorphism. Dual coordinates supply its
    analytic section and prove closedness in the exact metric. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP FiniteCoordinates HolomorphicCoordinateNorm HolomorphicAtUP Hom RealNormUP LinearBasis GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness NormAnalyticUP
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermMetric FieldPrefixCoordinatesSealed
  FieldPrefixCoordinateLaws HolomorphicPrefixMapRegularity HolomorphicPrefixGermMap
  HolomorphicCoordinateSubringSealed HolomorphicCoordinateImageClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PrefixSubring.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Hypothesis hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX.
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Variable j:nat.
Hypothesis hjn:(j<=n)%N.
Local Notation Y:=(coordinate_space (ComplexScalars.C R) j).
Local Notation NY:=(@holomorphic_coordinate_norm R j).
Local Notation hNY:=(complex_norm_real (@holomorphic_coordinate_norm_laws R j)).
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)].
Local Notation E:=(@holomorphic_prefix_germ_map R X NX hNX n e he omega j hjn).
Local Notation p:=(@FieldPrefixCoordinates.projection (ComplexScalars.C R) X n omega j hjn).

(** Source for [holomorphic_prefix_germ_subring]: the original
    Q_j=im O_0(p_j), 3.4.8(1), p. 326.
    Its selected image is hidden by independent membership laws. *)
Definition holomorphic_prefix_germ_subring:set G:=
  @HolomorphicCoordinateGermImage.value R X Y NX NY hNX hNY 0 0 E.

(** Source for [holomorphic_prefix_germ_subring_membership]: the
    exact original image condition for Q_j,
    3.4.8(1), p. 326. *)
Lemma holomorphic_prefix_germ_subring_membership (alpha:G):
  holomorphic_prefix_germ_subring alpha <->
    exists beta:@holomorphic_germ_ring R Y NY hNY 0,E beta=alpha.
Proof. exact:(@HolomorphicCoordinateGermImage.laws R X Y NX NY hNX hNY 0 0 E alpha). Qed.

(** Source for [holomorphic_prefix_germ_subring_closed]: the
    original coordinate subring is closed, as required
    in the proof of 3.4.8(5), p. 328.
    A continuous retraction proves this for the same image
    specified in (1), without an extra closedness premise. *)
Theorem holomorphic_prefix_germ_subring_closed:
  (forall i k,omega i (e k)=if i==k then 1 else 0) ->
  @closed (@holomorphic_germ_metric R X NX hNX 0) holomorphic_prefix_germ_subring.
Proof.
move=>hDual.
pose s:=@FieldPrefixCoordinates.inclusion (ComplexScalars.C R) X n e j hjn.
have hProjection:=@FieldPrefixCoordinates.projection_laws (ComplexScalars.C R) X n omega j hjn.
have hInclusion:=@FieldPrefixCoordinates.inclusion_laws (ComplexScalars.C R) X n e j hjn.
have hSection:=@field_prefix_projection_section (ComplexScalars.C R) X n e omega j hjn p s
  hDual hProjection hInclusion.
have hs:@is_holomorphic_at R Y X NY NX hNY hNX setT s 0.
  exists setT;split;first exact:Logic.I.
  split;first by move=>x _.
  exact:(@holomorphic_prefix_inclusion_holomorphic R X NX hNX j s).
have hs0:s 0=0:=linear0 s.
have hClosed:=@holomorphic_coordinate_pullback_image_closed R X Y NX NY hNX hNY
  setT setT p s 0 0 (@holomorphic_prefix_projection_at_origin R X NX hNX n e he omega j hjn)
  hs (@holomorphic_prefix_projection_zero R X n omega j hjn) hs0 hSection.
have hImage:(holomorphic_prefix_germ_subring:set (@holomorphic_germ_metric R X NX hNX 0))=
    (fun beta:@holomorphic_germ_metric R Y NY hNY 0=>(E beta:@holomorphic_germ_metric R X NX hNX 0)) @` setT.
  apply/seteqP;split.
  - move=>alpha /holomorphic_prefix_germ_subring_membership[beta hBeta].
    by exists beta.
  - move=>alpha [beta _ hBeta];apply/holomorphic_prefix_germ_subring_membership;by exists beta.
rewrite hImage.
exact:hClosed.
Qed.
End PrefixSubring.
