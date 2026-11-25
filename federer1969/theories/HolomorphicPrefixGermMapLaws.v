(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1), p. 326:
    the original prefix germ map retains every actual
    representative equation and every scalar constant. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP FiniteCoordinates HolomorphicCoordinateNorm Hom RealNormUP LinearBasis GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness HolomorphicGermRepresentatives HolomorphicGermArithmeticRepresentatives
  HolomorphicGermUP HolomorphicGermRing PointedHolomorphicPullbackUP PointedHolomorphicPullbackSealed
  PointedHolomorphicPullbackRing FieldPrefixCoordinatesSealed HolomorphicPrefixGermMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section MapLaws.
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
Local Notation p:=(@FieldPrefixCoordinates.projection (ComplexScalars.C R) X n omega j hjn).
Local Notation E:=(@holomorphic_prefix_germ_map R X NX hNX n e he omega j hjn).

(** Source for [holomorphic_prefix_germ_map_specification]: every
    original germ is pulled back by actual composition
    with p_j, 3.4.8(1), p. 326. *)
Lemma holomorphic_prefix_germ_map_specification:is_pointed_holomorphic_germ_pullback p E.
Proof.
exact:(@PointedHolomorphicPullback.laws R X Y NX NY hNX hNY _ p 0 0
  (@holomorphic_prefix_projection_at_origin R X NX hNX n e he omega j hjn)
  (@holomorphic_prefix_projection_zero R X n omega j hjn)).
Qed.

(** Source for [holomorphic_prefix_germ_map_constant]: scalar
    constants are unchanged by the original coordinate
    pullback, supporting Q_0=R in 3.4.8(1), p. 326. *)
Lemma holomorphic_prefix_germ_map_constant (c:ComplexScalars.C R):
  E (holomorphic_germ (@holomorphic_constant_representative R Y NY hNY 0 c))=
    holomorphic_germ (@holomorphic_constant_representative R X NX hNX 0 c).
Proof.
exact:(@pointed_holomorphic_pullback_constant R X Y NX NY hNX hNY 0 0 p E
  holomorphic_prefix_germ_map_specification c).
Qed.
End MapLaws.
