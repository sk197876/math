(** Federer (1969), 3.4.8(1),(5), pp. 326, 328:
    original prefix projections and their auxiliary inclusions
    hidden behind independent coordinate and basis laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom GrassmannAbbreviations AnalyticPrefixCoordinatesUP
  AnalyticPrefixProjectionExistence AnalyticPrefixSectionExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type AnalyticPrefixCoordinatesSignature.
(** Source for [projection]: the original p_j,
    supporting 3.4.8(1), p. 326. *)
Parameter projection:forall (R:realType) (X:lmodType R) n
  (omega:'I_n->Hom X R^o) j,(j<=n)%N ->Hom X (R_n R j).
(** Source for [inclusion]: the original basis gives
    the auxiliary coordinate inclusion, supporting
    3.4.8(1),(5), pp. 326, 328. *)
Parameter inclusion:forall (R:realType) (X:lmodType R) n
  (e:'I_n->X) j,(j<=n)%N ->Hom (R_n R j) X.
(** Source for [projection_laws]: the independent original
    coordinate equation of 3.4.8(1), p. 326. *)
Parameter projection_laws:forall (R:realType) (X:lmodType R) n
  (omega:'I_n->Hom X R^o) j (hjn:(j<=n)%N),
  is_analytic_prefix_projection omega hjn (@projection R X n omega j hjn).
(** Source for [inclusion_laws]: the independent basis
    equation for the inclusion supporting 3.4.8(1),(5),
    pp. 326, 328. *)
Parameter inclusion_laws:forall (R:realType) (X:lmodType R) n
  (e:'I_n->X) j (hjn:(j<=n)%N),
  is_analytic_prefix_section e hjn (@inclusion R X n e j hjn).
End AnalyticPrefixCoordinatesSignature.
Module AnalyticPrefixCoordinates:AnalyticPrefixCoordinatesSignature.
(** Source for [projection]: the hidden witness from
    proved existence, supporting 3.4.8(1), p. 326. *)
Definition projection (R:realType) (X:lmodType R) n
    (omega:'I_n->Hom X R^o) j (hjn:(j<=n)%N):=
  projT1 (cid (@analytic_prefix_projection_exists R X n omega j hjn)).
(** Source for [inclusion]: the hidden witness from
    proved existence, supporting 3.4.8(1),(5), pp. 326, 328. *)
Definition inclusion (R:realType) (X:lmodType R) n
    (e:'I_n->X) j (hjn:(j<=n)%N):=
  projT1 (cid (@analytic_prefix_section_exists R X n e j hjn)).
(** Source for [projection_laws]: the selected projection
    satisfies the original equation, 3.4.8(1), p. 326. *)
Lemma projection_laws (R:realType) (X:lmodType R) n
    (omega:'I_n->Hom X R^o) j (hjn:(j<=n)%N):
  is_analytic_prefix_projection omega hjn (@projection R X n omega j hjn).
Proof. exact:(projT2 (cid (@analytic_prefix_projection_exists R X n omega j hjn))). Qed.
(** Source for [inclusion_laws]: the selected inclusion
    satisfies the independent basis laws supporting
    3.4.8(1),(5), pp. 326, 328. *)
Lemma inclusion_laws (R:realType) (X:lmodType R) n
    (e:'I_n->X) j (hjn:(j<=n)%N):
  is_analytic_prefix_section e hjn (@inclusion R X n e j hjn).
Proof. exact:(projT2 (cid (@analytic_prefix_section_exists R X n e j hjn))). Qed.
End AnalyticPrefixCoordinates.
