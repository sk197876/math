(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1),
    p. 326: the original complex prefix projection induces
    a homomorphism of the actual holomorphic germ rings at zero.
    The coordinate maps and induced germ maps remain opaque. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP FiniteCoordinates
  LinearBasis HolomorphicAtUP HolomorphicGermUP HolomorphicGermRing PointedHolomorphicPullbackSealed
  PointedHolomorphicPullbackRingMorphism FieldPrefixCoordinatesSealed HolomorphicCoordinateNorm
  HolomorphicPrefixMapRegularity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PrefixGerms.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Variable j:nat.
Variable hjn:(j<=n)%N.
Local Notation Y:=(coordinate_space (ComplexScalars.C R) j).
Local Notation NY:=(@holomorphic_coordinate_norm R j).
Local Notation hNY:=(complex_norm_real (@holomorphic_coordinate_norm_laws R j)).
Local Notation p:=(@FieldPrefixCoordinates.projection (ComplexScalars.C R) X n omega j hjn).

(** Source for [holomorphic_prefix_projection_at_origin]: the original
    complex p_j is holomorphic near zero, extending 3.4.8(1), p. 326. *)
Lemma holomorphic_prefix_projection_at_origin:
  @is_holomorphic_at R X Y NX NY hNX hNY setT p 0.
Proof.
exists setT;split;first exact:Logic.I.
split;first by move=>x _.
exact:(@holomorphic_prefix_projection_holomorphic R X NX hNX n e he j p).
Qed.

(** Source for [holomorphic_prefix_projection_zero]: the original
    complex linear p_j preserves zero, extending 3.4.8(1), p. 326. *)
Lemma holomorphic_prefix_projection_zero:p 0=0.
Proof. exact:linear0 p. Qed.

(** Source for [holomorphic_prefix_germ_map]: the original
    homomorphism O^C_0(p_j), extending 3.4.8(1), p. 326.
    The independent pointed representative laws specify its values. *)
Definition holomorphic_prefix_germ_map:
  {rmorphism [the comNzRingType of (@holomorphic_germ_ring R Y NY hNY 0)]->
    [the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)]}:=
  @pointed_holomorphic_germ_ring_pullback R X Y NX NY hNX hNY p 0 0
    (@PointedHolomorphicPullback.map R X Y NX NY hNX hNY setT p 0 0
      holomorphic_prefix_projection_at_origin holomorphic_prefix_projection_zero)
    (@PointedHolomorphicPullback.laws R X Y NX NY hNX hNY setT p 0 0
      holomorphic_prefix_projection_at_origin holomorphic_prefix_projection_zero).
End PrefixGerms.
