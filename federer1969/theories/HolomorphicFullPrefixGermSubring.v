(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1),(11), pp. 326,
    333: the full coordinate subring Q_n
    is the whole original holomorphic germ ring.
    Reuse the existing pointed pullback retraction
    theorem and the original dual-basis equations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP FiniteCoordinates HolomorphicCoordinateNorm FieldFullPrefixInverse HolomorphicAtUP Hom TensorUP RealNormUP LinearBasis GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness HolomorphicGermRing FieldPrefixCoordinatesSealed
  FieldPrefixCoordinateLaws FieldPrefixBasisValues HolomorphicPrefixMapRegularity HolomorphicPrefixGermMap
  HolomorphicPrefixGermMapLaws PointedHolomorphicPullbackSealed PointedHolomorphicPullbackRetraction
  HolomorphicPrefixGermSubring HolomorphicCoordinateSubringFamilyUP HolomorphicCoordinateSubringFamilySealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_full_prefix_germ_subring]:
    a nonzero original ideal has a
    nonzero member in Q_n, used in
    3.4.8(11), p. 333. The full
    coordinate inverse proves the stronger exact
    equality Q_n=O_0(X). *)
Theorem holomorphic_full_prefix_germ_subring (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) n (e:'I_n->X) (he:is_basis e)
    (omega:'I_n->Hom X (ComplexScalars.C R)^o)
    (hDual:forall i j,omega i (e j) = if i==j then 1 else 0):
  @HolomorphicCoordinateSubringFamily.value R X NX hNX n e he omega n = setT.
Proof.
pose Y:=coordinate_space (ComplexScalars.C R) n.
pose NY:=@holomorphic_coordinate_norm R n.
pose hNY:=complex_norm_real (@holomorphic_coordinate_norm_laws R n).
pose P:=@FieldPrefixCoordinates.projection (ComplexScalars.C R) X n omega n (leqnn n).
pose S:=@FieldPrefixCoordinates.inclusion (ComplexScalars.C R) X n e n (leqnn n).
pose E:=@holomorphic_prefix_germ_map R X NX hNX n e he omega n (leqnn n).
have hP:=@FieldPrefixCoordinates.projection_laws (ComplexScalars.C R) X n omega n (leqnn n).
have hS:=@FieldPrefixCoordinates.inclusion_laws (ComplexScalars.C R) X n e n (leqnn n).
have hSP:=@field_full_prefix_inverse (ComplexScalars.C R) X n e he omega P S hDual hP hS.
have hHolomorphic:@is_holomorphic_at R Y X NY NX hNY hNX setT S 0.
  exists setT;split;first exact:Logic.I.
  split;first by move=>x _.
  exact:(@holomorphic_prefix_inclusion_holomorphic R X NX hNX n S).
pose T:=@PointedHolomorphicPullback.map R Y X NY NX hNY hNX setT S 0 0 hHolomorphic (linear0 S).
have hT:=@PointedHolomorphicPullback.laws R Y X NY NX hNY hNX setT S 0 0 hHolomorphic (linear0 S).
have hE:=@holomorphic_prefix_germ_map_specification R X NX hNX n e he omega n (leqnn n).
have hCancel:=@pointed_holomorphic_germ_pullback_retraction R Y X NY NX hNY hNX 0 0
  S P T E hT hE hSP.
have hQ:=@HolomorphicCoordinateSubringFamily.laws R X NX hNX n e he omega.
rewrite (holomorphic_coordinate_subring_family_member hQ (leqnn n)).
apply/seteqP;split=>alpha _;first exact:Logic.I.
apply/holomorphic_prefix_germ_subring_membership;exists (T alpha);exact:hCancel alpha.
Qed.
