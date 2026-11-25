(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1), p. 326:
    existence and uniqueness of the original family
    of coordinate germ images, using only each
    image's public opaque interface. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP Hom RealNormUP LinearBasis HolomorphicGermRing HolomorphicPrefixGermSubring
  HolomorphicCoordinateSubringFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_coordinate_subring_family_exists]:
    the original finite-prefix images supply an
    actual family, as in 3.4.8(1), p. 326.
    Only unused indices receive an auxiliary extension. *)
Theorem holomorphic_coordinate_subring_family_exists (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X (ComplexScalars.C R)^o):
  exists Q:nat->set (@holomorphic_germ_ring R X NX hNX 0),
    is_holomorphic_coordinate_subring_family he omega Q.
Proof.
pose Q:=fun j=>if pselect ((j<=n)%N) is left h then
  @holomorphic_prefix_germ_subring R X NX hNX n e he omega j h else set0.
exists Q;constructor.
- move=>j hj;rewrite /Q;case:pselect=>[h|h].
  + by rewrite (bool_irrelevance h hj).
  + exfalso;exact:h hj.
- move=>j hj;rewrite /Q;case:pselect=>[h|h]=>//.
  have hFalse:=leq_ltn_trans h hj;by rewrite ltnn in hFalse.
Qed.

(** Source for [holomorphic_coordinate_subring_family_unique]:
    the exact independent image laws determine the
    family uniquely, supporting 3.4.8(1), p. 326. *)
Lemma holomorphic_coordinate_subring_family_unique (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X (ComplexScalars.C R)^o) (Q P:nat->set (@holomorphic_germ_ring R X NX hNX 0)):
  is_holomorphic_coordinate_subring_family he omega Q ->
  is_holomorphic_coordinate_subring_family he omega P ->Q = P.
Proof.
move=>hQ hP;apply:funext=>j;case:(leqP j n)=>[hj|hj].
- by rewrite (holomorphic_coordinate_subring_family_member hQ hj)
    (holomorphic_coordinate_subring_family_member hP hj).
- by rewrite (holomorphic_coordinate_subring_family_outside hQ hj)
    (holomorphic_coordinate_subring_family_outside hP hj).
Qed.
