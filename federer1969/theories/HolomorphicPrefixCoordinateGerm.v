(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1),(8), pp. 326, 329:
    the last coordinate germ of each actual
    prefix maps to the original gamma_j.
    Apply the all-representative coordinate laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP FiniteCoordinates HolomorphicCoordinateNorm Hom RealNormUP LinearBasis GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness HolomorphicGermUP HolomorphicGermRepresentatives
  FieldPrefixCoordinatesSealed HolomorphicPrefixGermMap HolomorphicPrefixGermMapLaws
  HolomorphicCoordinateGermsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [holomorphic_prefix_last_coordinate_germ]: the
    original coordinate classes in p(Q_j) are
    exactly the gamma_j classes used in
    3.4.8(8), p. 329. This retains every
    original linear-coordinate representative. *)
Theorem holomorphic_prefix_last_coordinate_germ (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:X->R) (hNX:is_complex_norm NX) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X (ComplexScalars.C R)^o) (j:'I_n)
  (f:@holomorphic_representative_type R (coordinate_space (ComplexScalars.C R) (j:nat).+1)
    (@holomorphic_coordinate_norm R (j:nat).+1)
    (complex_norm_real (@holomorphic_coordinate_norm_laws R (j:nat).+1)) 0):
  (forall y,holomorphic_representative_value f y = y ord_max) ->
  @holomorphic_prefix_germ_map R X NX (complex_norm_real hNX) n e he omega (j:nat).+1 (ltn_ord j) (holomorphic_germ f) =
    @HolomorphicCoordinateGerms.value R X NX hNX n e he omega j.
Proof.
move=>hF.
pose P:=@FieldPrefixCoordinates.projection (ComplexScalars.C R) X n omega (j:nat).+1 (ltn_ord j).
have hProjection:=@FieldPrefixCoordinates.projection_laws (ComplexScalars.C R) X n omega (j:nat).+1 (ltn_ord j).
have hPullback:=@holomorphic_prefix_germ_map_specification R X NX (complex_norm_real hNX) n e he omega (j:nat).+1 (ltn_ord j).
have [g [hG hValues]]:=hPullback f.
rewrite hG.
apply:(@HolomorphicCoordinateGerms.laws R X NX hNX n e he omega j g)=>x.
rewrite hValues hF hProjection.
have hIndex:widen_ord (ltn_ord j) (ord_max:'I_(j:nat).+1) = j by apply:val_inj.
by rewrite hIndex.
Qed.
