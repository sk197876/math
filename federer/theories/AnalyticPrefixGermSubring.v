(** Federer (1969), 3.4.8(1),(5), pp. 326, 328:
    the original Q_j is the opaque image of the actual
    prefix germ homomorphism. Dual coordinates supply its
    analytic section and prove closedness in the exact metric. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP LinearBasis GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness NormAnalyticUP
  AnalyticGermUP AnalyticGermRing AnalyticGermMetric AnalyticPrefixCoordinatesSealed
  AnalyticPrefixCoordinateLaws AnalyticPrefixMapRegularity AnalyticPrefixGermMap
  AnalyticCoordinateSubringSealed AnalyticCoordinateImageClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PrefixSubring.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Variable omega:'I_n->Hom X R^o.
Variable j:nat.
Hypothesis hjn:(j<=n)%N.
Local Notation Y:=(R_n R j).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R j)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R j)).
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation E:=(@analytic_prefix_germ_map R X NX hNX n e he omega j hjn).
Local Notation p:=(@AnalyticPrefixCoordinates.projection R X n omega j hjn).

(** Source for [analytic_prefix_germ_subring]: the original
    Q_j=im O_0(p_j), 3.4.8(1), p. 326.
    Its selected image is hidden by independent membership laws. *)
Definition analytic_prefix_germ_subring:set G:=
  @AnalyticCoordinateGermImage.value R X Y NX NY hNX hNY 0 0 E.

(** Source for [analytic_prefix_germ_subring_membership]: the
    exact original image condition for Q_j,
    3.4.8(1), p. 326. *)
Lemma analytic_prefix_germ_subring_membership (alpha:G):
  analytic_prefix_germ_subring alpha <->
    exists beta:@analytic_germ_ring R Y NY hNY 0,E beta=alpha.
Proof. exact:(@AnalyticCoordinateGermImage.laws R X Y NX NY hNX hNY 0 0 E alpha). Qed.

(** Source for [analytic_prefix_germ_subring_closed]: the
    original coordinate subring is closed, as required
    in the proof of 3.4.8(5), p. 328.
    A continuous retraction proves this for the same image
    specified in (1), without an extra closedness premise. *)
Theorem analytic_prefix_germ_subring_closed:
  (forall i k,omega i (e k)=if i==k then 1 else 0) ->
  @closed (@analytic_germ_metric R X NX hNX 0) analytic_prefix_germ_subring.
Proof.
move=>hDual.
pose s:=@AnalyticPrefixCoordinates.inclusion R X n e j hjn.
have hProjection:=@AnalyticPrefixCoordinates.projection_laws R X n omega j hjn.
have hInclusion:=@AnalyticPrefixCoordinates.inclusion_laws R X n e j hjn.
have hSection:=@analytic_prefix_projection_section R X n e omega j hjn p s
  hDual hProjection hInclusion.
have hs:@norm_analytic_at R Y X NY NX hNY hNX setT s 0:=
  (@analytic_prefix_inclusion_analytic R X NX hNX j s) 0 Logic.I.
have hs0:s 0=0:=linear0 s.
have hClosed:=@analytic_coordinate_pullback_image_closed R X Y NX NY hNX hNY
  setT setT p s 0 0 (@analytic_prefix_projection_at_origin R X NX hNX n e he omega j hjn)
  hs (@analytic_prefix_projection_zero R X n omega j hjn) hs0 hSection.
have hImage:(analytic_prefix_germ_subring:set (@analytic_germ_metric R X NX hNX 0))=
    (fun beta:@analytic_germ_metric R Y NY hNY 0=>(E beta:@analytic_germ_metric R X NX hNX 0)) @` setT.
  apply/seteqP;split.
  - move=>alpha /analytic_prefix_germ_subring_membership[beta hBeta].
    by exists beta.
  - move=>alpha [beta _ hBeta];apply/analytic_prefix_germ_subring_membership;by exists beta.
rewrite hImage.
exact:hClosed.
Qed.
End PrefixSubring.
