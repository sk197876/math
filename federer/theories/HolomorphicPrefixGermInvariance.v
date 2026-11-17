(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.8(6), p. 329:
    actual holomorphic pullback by a fixed-tail linear
    map preserves the original coordinate subring Q_p.
    The exact original square and representative laws
    prove the assertion; it is not a premise. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP FiniteCoordinates HolomorphicCoordinateNorm FieldPrefixCoordinatesSealed Hom RealNormUP LinearBasis GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness HolomorphicAtUP HolomorphicUP HolomorphicGermUP HolomorphicGermRing
  PointedHolomorphicPullbackUP PointedHolomorphicPullbackSealed PointedHolomorphicImagePreservation
  FieldPrefixCoordinatesSealed HolomorphicPrefixMapRegularity HolomorphicPrefixGermMap
  HolomorphicPrefixGermMapLaws HolomorphicPrefixGermSubring FieldPrefixFixedTailSquare.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_prefix_germ_subring_invariant]: the
    original Q_p is preserved by the actual maps
    fixing the tail, as used in 3.4.8(6), p. 329. *)
Theorem holomorphic_prefix_germ_subring_invariant (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X (ComplexScalars.C R)^o) p (hPN:(p<=n)%N) (H:Hom X X)
  (M:@holomorphic_germ_ring R X NX hNX 0->@holomorphic_germ_ring R X NX hNX 0):
  (forall i k,omega i (e k) = if i==k then 1 else 0) ->
  is_pointed_holomorphic_germ_pullback H M ->
  (forall i:'I_n,(p<=i)%N ->H (e i) = e i) ->
  forall alpha,@holomorphic_prefix_germ_subring R X NX hNX n e he omega p hPN alpha ->
    @holomorphic_prefix_germ_subring R X NX hNX n e he omega p hPN (M alpha).
Proof.
move=>hDual hM hFixed alpha /holomorphic_prefix_germ_subring_membership[beta <-].
pose Y:=coordinate_space (ComplexScalars.C R) p.
pose NY:=@holomorphic_coordinate_norm R p.
pose hNY:=complex_norm_real (@holomorphic_coordinate_norm_laws R p).
pose projection:=@FieldPrefixCoordinates.projection (ComplexScalars.C R) X n omega p hPN.
pose section:=@FieldPrefixCoordinates.inclusion (ComplexScalars.C R) X n e p hPN.
pose P:=@holomorphic_prefix_germ_map R X NX hNX n e he omega p hPN.
have hSection:@is_holomorphic_at R Y X NY NX hNY hNX setT section 0.
  exists setT;split;first exact:Logic.I.
  split;first by move=>x _.
  exact:(@holomorphic_prefix_inclusion_holomorphic R X NX hNX p section).
have hSectionZero:section 0 = 0:=linear0 section.
pose S:=@PointedHolomorphicPullback.map R Y X NY NX hNY hNX setT section 0 0 hSection hSectionZero.
have hS:=@PointedHolomorphicPullback.laws R Y X NY NX hNY hNX setT section 0 0 hSection hSectionZero.
have hP:=@holomorphic_prefix_germ_map_specification R X NX hNX n e he omega p hPN.
have hSquare:=@field_prefix_fixed_tail_square (ComplexScalars.C R) X n e he omega p hPN projection section H hDual
  (@FieldPrefixCoordinates.projection_laws (ComplexScalars.C R) X n omega p hPN)
  (@FieldPrefixCoordinates.inclusion_laws (ComplexScalars.C R) X n e p hPN) hFixed.
apply/holomorphic_prefix_germ_subring_membership;exists (S (M (P beta))).
exact:(@pointed_holomorphic_image_preservation R X Y NX NY hNX hNY 0 0
  projection section H P S M hP hS hM hSquare beta).
Qed.
