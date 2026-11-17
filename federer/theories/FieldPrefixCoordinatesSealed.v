(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1),(5), pp. 326, 328:
    original prefix projections and their auxiliary inclusions
    hidden behind independent coordinate and basis laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import Hom FiniteCoordinates FieldPrefixCoordinatesUP
  FieldPrefixProjectionExistence FieldPrefixSectionExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type FieldPrefixCoordinatesSignature.
(** Source for [projection]: the original p_j,
    supporting 3.4.8(1), p. 326. *)
Parameter projection:forall (K:fieldType) (X:lmodType K) n
  (omega:'I_n->Hom X K^o) j,(j<=n)%N ->Hom X (coordinate_space K j).
(** Source for [inclusion]: the original basis gives
    the auxiliary coordinate inclusion, supporting
    3.4.8(1),(5), pp. 326, 328. *)
Parameter inclusion:forall (K:fieldType) (X:lmodType K) n
  (e:'I_n->X) j,(j<=n)%N ->Hom (coordinate_space K j) X.
(** Source for [projection_laws]: the independent original
    coordinate equation of 3.4.8(1), p. 326. *)
Parameter projection_laws:forall (K:fieldType) (X:lmodType K) n
  (omega:'I_n->Hom X K^o) j (hjn:(j<=n)%N),
  is_field_prefix_projection omega hjn (@projection K X n omega j hjn).
(** Source for [inclusion_laws]: the independent basis
    equation for the inclusion supporting 3.4.8(1),(5),
    pp. 326, 328. *)
Parameter inclusion_laws:forall (K:fieldType) (X:lmodType K) n
  (e:'I_n->X) j (hjn:(j<=n)%N),
  is_field_prefix_section e hjn (@inclusion K X n e j hjn).
End FieldPrefixCoordinatesSignature.
Module FieldPrefixCoordinates:FieldPrefixCoordinatesSignature.
(** Source for [projection]: the hidden witness from
    proved existence, supporting 3.4.8(1), p. 326. *)
Definition projection (K:fieldType) (X:lmodType K) n
    (omega:'I_n->Hom X K^o) j (hjn:(j<=n)%N):=
  projT1 (cid (@field_prefix_projection_exists K X n omega j hjn)).
(** Source for [inclusion]: the hidden witness from
    proved existence, supporting 3.4.8(1),(5), pp. 326, 328. *)
Definition inclusion (K:fieldType) (X:lmodType K) n
    (e:'I_n->X) j (hjn:(j<=n)%N):=
  projT1 (cid (@field_prefix_section_exists K X n e j hjn)).
(** Source for [projection_laws]: the selected projection
    satisfies the original equation, 3.4.8(1), p. 326. *)
Lemma projection_laws (K:fieldType) (X:lmodType K) n
    (omega:'I_n->Hom X K^o) j (hjn:(j<=n)%N):
  is_field_prefix_projection omega hjn (@projection K X n omega j hjn).
Proof. exact:(projT2 (cid (@field_prefix_projection_exists K X n omega j hjn))). Qed.
(** Source for [inclusion_laws]: the selected inclusion
    satisfies the independent basis laws supporting
    3.4.8(1),(5), pp. 326, 328. *)
Lemma inclusion_laws (K:fieldType) (X:lmodType K) n
    (e:'I_n->X) j (hjn:(j<=n)%N):
  is_field_prefix_section e hjn (@inclusion K X n e j hjn).
Proof. exact:(projT2 (cid (@field_prefix_section_exists K X n e j hjn))). Qed.
End FieldPrefixCoordinates.
