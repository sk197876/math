(** Federer (1969), 4.1.11, p. 366: hide
    the coordinate existence witnesses for H, f and g.
    Consumers use only their independently specified
    original formulas; current associativity remains a theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import GrassmannAbbreviations CurrentJoinAssociatorMapsUP
  CurrentJoinAssociatorMapsExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type CurrentJoinAssociatorMapsSignature.
(** Source for [barycentre]: Federer's original H,
    Federer 4.1.11, p. 366. *)
Parameter barycentre:forall (R:realType) n,R_n R (n+(n+(n+3)))%N->R_n R n.
(** Source for [barycentre_laws]: exactly the original
    printed coordinate formula for H, Federer 4.1.11,
    p. 366. *)
Parameter barycentre_laws:forall (R:realType) n,
  @is_current_join_barycentre R n (@barycentre R n).
(** Source for [left_triangle]: the original time-square
    map f, Federer 4.1.11, p. 366. *)
Parameter left_triangle:forall R:realType,R_n R 2%N->R_n R 3%N.
(** Source for [left_triangle_laws]: the original formula
    for f, Federer 4.1.11, p. 366. *)
Parameter left_triangle_laws:forall R:realType,
  @is_current_join_left_triangle_map R (@left_triangle R).
(** Source for [right_triangle]: the original time-square
    map g, Federer 4.1.11, p. 366. *)
Parameter right_triangle:forall R:realType,R_n R 2%N->R_n R 3%N.
(** Source for [right_triangle_laws]: the original formula
    for g, Federer 4.1.11, p. 366. *)
Parameter right_triangle_laws:forall R:realType,
  @is_current_join_right_triangle_map R (@right_triangle R).
End CurrentJoinAssociatorMapsSignature.
Module CurrentJoinAssociatorMaps:CurrentJoinAssociatorMapsSignature.
(** Source for [barycentre]: seal the proved original coordinate
    witness and its laws, Federer 4.1.11, p. 366. *)
Definition barycentre (R:realType) n:R_n R (n+(n+(n+3)))%N->R_n R n:=
  projT1 (cid (@current_join_barycentre_exists R n)).
(** Source for [barycentre_laws]: seal the proved original coordinate
    witness and its laws, Federer 4.1.11, p. 366. *)
Lemma barycentre_laws (R:realType) n:@is_current_join_barycentre R n (@barycentre R n).
Proof. exact:(projT2 (cid (@current_join_barycentre_exists R n))). Qed.
(** Source for [left_triangle]: seal the proved original coordinate
    witness and its laws, Federer 4.1.11, p. 366. *)
Definition left_triangle (R:realType):R_n R 2%N->R_n R 3%N:=
  projT1 (cid (@current_join_left_triangle_map_exists R)).
(** Source for [left_triangle_laws]: seal the proved original coordinate
    witness and its laws, Federer 4.1.11, p. 366. *)
Lemma left_triangle_laws (R:realType):@is_current_join_left_triangle_map R (@left_triangle R).
Proof. exact:(projT2 (cid (@current_join_left_triangle_map_exists R))). Qed.
(** Source for [right_triangle]: seal the proved original coordinate
    witness and its laws, Federer 4.1.11, p. 366. *)
Definition right_triangle (R:realType):R_n R 2%N->R_n R 3%N:=
  projT1 (cid (@current_join_right_triangle_map_exists R)).
(** Source for [right_triangle_laws]: seal the proved original coordinate
    witness and its laws, Federer 4.1.11, p. 366. *)
Lemma right_triangle_laws (R:realType):@is_current_join_right_triangle_map R (@right_triangle R).
Proof. exact:(projT2 (cid (@current_join_right_triangle_map_exists R))). Qed.
End CurrentJoinAssociatorMaps.
