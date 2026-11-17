(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1), p. 326:
    the original coordinate subrings Q_j form one
    family. Every legal member is the actual
    prefix germ image. Indices above n are assigned
    the empty set solely to give a total auxiliary
    array; no source assertion uses those indices. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP Hom RealNormUP LinearBasis HolomorphicGermRing HolomorphicPrefixGermSubring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_holomorphic_coordinate_subring_family]:
    every original Q_j is precisely the image
    of the original p_j pullback, 3.4.8(1),
    p. 326. These independent laws include no
    Borel, dimension or stratification conclusion. *)
Record is_holomorphic_coordinate_subring_family (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X (ComplexScalars.C R)^o)
  (Q:nat->set (@holomorphic_germ_ring R X NX hNX (0%R:X))):Prop:={
  (** Source for [holomorphic_coordinate_subring_family_member]:
      the exact original image at every legal
      prefix, 3.4.8(1), p. 326. *)
  holomorphic_coordinate_subring_family_member:forall j (hjn:(j<=n)%N),
    Q j = @holomorphic_prefix_germ_subring R X NX hNX n e he omega j hjn;
  (** Source for [holomorphic_coordinate_subring_family_outside]:
      the unused total-array extension adds no
      mathematical member beyond the original family
      j<=n of 3.4.8(1), p. 326. *)
  holomorphic_coordinate_subring_family_outside:forall j,(n<j)%N ->Q j = set0
}.
