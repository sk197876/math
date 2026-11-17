(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1), p. 326:
    the original coordinate germ image is a subring.
    Its independent image membership laws and the actual
    ring homomorphism prove every closure property. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP FiniteCoordinates HolomorphicCoordinateNorm Hom RealNormUP LinearBasis GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness HolomorphicGermUP HolomorphicGermRing
  CommutativeSubringUP FieldPrefixCoordinatesSealed HolomorphicPrefixGermMap HolomorphicPrefixGermSubring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section RingLaws.
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


(** Source for [holomorphic_prefix_germ_subring_laws]: zero,
    one, addition, negation, and multiplication belong to
    the original Q_j, 3.4.8(1), p. 326. *)
Theorem holomorphic_prefix_germ_subring_laws:
  is_commutative_subring (@holomorphic_prefix_germ_subring R X NX hNX n e he omega j hjn).
Proof.
constructor.
- apply/holomorphic_prefix_germ_subring_membership;exists 0;exact:rmorph0.
- apply/holomorphic_prefix_germ_subring_membership;exists 1;exact:rmorph1.
- move=>alpha beta /holomorphic_prefix_germ_subring_membership[x <-]
    /holomorphic_prefix_germ_subring_membership[y <-].
  apply/holomorphic_prefix_germ_subring_membership;exists (x+y);exact:rmorphD.
- move=>alpha /holomorphic_prefix_germ_subring_membership[x <-].
  apply/holomorphic_prefix_germ_subring_membership;exists (-x);exact:rmorphN.
- move=>alpha beta /holomorphic_prefix_germ_subring_membership[x <-]
    /holomorphic_prefix_germ_subring_membership[y <-].
  apply/holomorphic_prefix_germ_subring_membership;exists (x*y);exact:rmorphM.
Qed.
End RingLaws.
