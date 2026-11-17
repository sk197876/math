(** Federer (1969), 3.4.8(1), p. 326:
    the original coordinate subrings Q_j form one
    family. Every legal member is the actual
    prefix germ image. Indices above n are assigned
    the empty set solely to give a total auxiliary
    array; no source assertion uses those indices. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP LinearBasis AnalyticGermRing AnalyticPrefixGermSubring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_analytic_coordinate_subring_family]:
    every original Q_j is precisely the image
    of the original p_j pullback, 3.4.8(1),
    p. 326. These independent laws include no
    Borel, dimension or stratification conclusion. *)
Record is_analytic_coordinate_subring_family (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X R^o)
  (Q:nat->set (@analytic_germ_ring R X NX hNX (0%R:X))):Prop:={
  (** Source for [analytic_coordinate_subring_family_member]:
      the exact original image at every legal
      prefix, 3.4.8(1), p. 326. *)
  analytic_coordinate_subring_family_member:forall j (hjn:(j<=n)%N),
    Q j = @analytic_prefix_germ_subring R X NX hNX n e he omega j hjn;
  (** Source for [analytic_coordinate_subring_family_outside]:
      the unused total-array extension adds no
      mathematical member beyond the original family
      j<=n of 3.4.8(1), p. 326. *)
  analytic_coordinate_subring_family_outside:forall j,(n<j)%N ->Q j = set0
}.
