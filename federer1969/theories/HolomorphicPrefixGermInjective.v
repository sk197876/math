(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1),(10),
    pp. 326, 330: the original holomorphic prefix pullback
    is injective. Apply the existing pointed retraction theorem to
    the actual original coordinate section, including an empty prefix. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  LinearBasis FiniteCoordinates HolomorphicCoordinateNorm HolomorphicAtUP HolomorphicGermRing
  FieldPrefixCoordinatesSealed FieldPrefixCoordinateLaws HolomorphicPrefixMapRegularity
  HolomorphicPrefixGermMap HolomorphicPrefixGermMapLaws
  PointedHolomorphicPullbackSealed PointedHolomorphicPullbackRetraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
(** Source for [holomorphic_prefix_germ_map_injective]: the original
    prefix ring is an isomorphic copy of the original smaller
    holomorphic germ ring, 3.4.12, p. 339. *)
Theorem holomorphic_prefix_germ_map_injective (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX)
  n (e:'I_n->X) (he:is_basis e) (omega:'I_n->Hom X (ComplexScalars.C R)^o)
  (hDual:forall i j,omega i (e j)=if i==j then 1 else 0) m (hMN:(m<=n)%N):
  injective (@holomorphic_prefix_germ_map R X NX hNX n e he omega m hMN).
Proof.
pose Y:=coordinate_space (ComplexScalars.C R) m.
pose NY:=@holomorphic_coordinate_norm R m.
pose hNY:=complex_norm_real (@holomorphic_coordinate_norm_laws R m).
pose P:=@FieldPrefixCoordinates.projection (ComplexScalars.C R) X n omega m hMN.
pose S:=@FieldPrefixCoordinates.inclusion (ComplexScalars.C R) X n e m hMN.
pose E:=@holomorphic_prefix_germ_map R X NX hNX n e he omega m hMN.
have hP:=@FieldPrefixCoordinates.projection_laws (ComplexScalars.C R) X n omega m hMN.
have hS:=@FieldPrefixCoordinates.inclusion_laws (ComplexScalars.C R) X n e m hMN.
have hSection:=@field_prefix_projection_section (ComplexScalars.C R) X n e omega m hMN P S hDual hP hS.
have hHolomorphic:@is_holomorphic_at R Y X NY NX hNY hNX setT S 0.
  exists setT;split;first exact:Logic.I.
  split;first by move=>x _.
  exact:(@holomorphic_prefix_inclusion_holomorphic R X NX hNX m S).
pose T:=@PointedHolomorphicPullback.map R Y X NY NX hNY hNX setT S 0 0 hHolomorphic (linear0 S).
have hT:=@PointedHolomorphicPullback.laws R Y X NY NX hNY hNX setT S 0 0 hHolomorphic (linear0 S).
have hE:=@holomorphic_prefix_germ_map_specification R X NX hNX n e he omega m hMN.
have hCancel:=@pointed_holomorphic_germ_pullback_retraction R X Y NX NY hNX hNY 0 0 P S E T hE hT hSection.
exact:can_inj hCancel.
Qed.
