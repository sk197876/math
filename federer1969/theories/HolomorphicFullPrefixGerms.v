(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1),(8),
    pp. 326, 329: the original full-prefix pullback is onto.
    Reuse the proved equality Q_n=O^C_0(X). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed LinearBasis HolomorphicGermRing
  HolomorphicCoordinateSubringFamilyUP HolomorphicCoordinateSubringFamilySealed
  HolomorphicPrefixGermSubring HolomorphicPrefixGermMap HolomorphicFullPrefixGermSubring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_full_prefix_germ_map_surjective]: the
    full coordinate image is the whole original holomorphic germ
    ring, 3.4.12, p. 339, including dimension zero. *)
Theorem holomorphic_full_prefix_germ_map_surjective (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX)
    n (e:'I_n->X) (he:is_basis e) (omega:'I_n->Hom X (ComplexScalars.C R)^o)
    (hDual:forall i j,omega i (e j)=if i==j then 1 else 0):
  forall alpha:@holomorphic_germ_ring R X NX hNX 0,
    exists beta,@holomorphic_prefix_germ_map R X NX hNX n e he omega n (leqnn n) beta=alpha.
Proof.
move=>alpha.
have hWhole:=@holomorphic_full_prefix_germ_subring R X NX hNX n e he omega hDual.
have hMember:@HolomorphicCoordinateSubringFamily.value R X NX hNX n e he omega n alpha.
  by rewrite hWhole.
rewrite (holomorphic_coordinate_subring_family_member
  (@HolomorphicCoordinateSubringFamily.laws R X NX hNX n e he omega) (leqnn n)) in hMember.
exact:(@holomorphic_prefix_germ_subring_membership R X NX hNX n e he omega n (leqnn n) alpha).1 hMember.
Qed.
