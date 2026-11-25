(** Federer (1969), 3.4.8(1),(8), pp. 326, 329:
    the last coordinate germ of each actual
    prefix maps to the original gamma_j.
    Apply the all-representative coordinate laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP LinearBasis GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness AnalyticGermUP AnalyticGermRepresentatives
  AnalyticPrefixCoordinatesSealed AnalyticPrefixGermMap AnalyticPrefixGermMapLaws
  AnalyticCoordinateGermsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [analytic_prefix_last_coordinate_germ]: the
    original coordinate classes in p(Q_j) are
    exactly the gamma_j classes used in
    3.4.8(8), p. 329. This retains every
    original linear-coordinate representative. *)
Theorem analytic_prefix_last_coordinate_germ (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X R^o) (j:'I_n)
  (f:@analytic_representative_type R (R_n R (j:nat).+1)
    (inner_norm (@euclidean_inner_productP R (j:nat).+1))
    (inner_norm_real_norm (@euclidean_inner_productP R (j:nat).+1)) 0):
  (forall y,analytic_representative_value f y = y ord_max) ->
  @analytic_prefix_germ_map R X NX hNX n e he omega (j:nat).+1 (ltn_ord j) (analytic_germ f) =
    @AnalyticCoordinateGerms.value R X NX hNX n e he omega j.
Proof.
move=>hF.
pose P:=@AnalyticPrefixCoordinates.projection R X n omega (j:nat).+1 (ltn_ord j).
have hProjection:=@AnalyticPrefixCoordinates.projection_laws R X n omega (j:nat).+1 (ltn_ord j).
have hPullback:=@analytic_prefix_germ_map_specification R X NX hNX n e he omega (j:nat).+1 (ltn_ord j).
have [g [hG hValues]]:=hPullback f.
rewrite hG.
apply:(@AnalyticCoordinateGerms.laws R X NX hNX n e he omega j g)=>x.
rewrite hValues hF hProjection.
have hIndex:widen_ord (ltn_ord j) (ord_max:'I_(j:nat).+1) = j by apply:val_inj.
by rewrite hIndex.
Qed.
