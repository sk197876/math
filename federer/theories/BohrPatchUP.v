(** Local finite-group laws supporting Federer (1969),
    2.8.20, p. 152; Saks1934 Lemma B, pp. 258–259,
    and Cesari1939 Lemma III, pp. 306–307. A patch
    lies in a positive half-open parent rectangle. Its closed
    companions are the eligible compact rectangles; a positive
    common core supports a measure with large averages. The
    harmonic gain controls the remaining area. Existence is
    separate from these laws. Source titles: VitaliMassObstruction.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import ScalarPlaneRectangles ScalarHalfOpenRectangles HarmonicPrefixBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [are_rectangle_companions]: auxiliary half-open
    and closed versions of one positive rectangle in the
    packing supporting Federer 2.8.20, p. 152. *)
Definition are_rectangle_companions (R : realType) (H K : set (R*R)) :=
  exists a b c d : R, (a<b)%R /\ (c<d)%R /\
    H = scalar_half_open_rectangle a b c d /\ K = scalar_closed_rectangle a b c d.

(** Source for [is_rectangle_lower_corner]: auxiliary minimum
    corner of a remaining rectangle for Federer 2.8.20,
    p. 152. This intrinsic predicate avoids choosing endpoints. *)
Definition is_rectangle_lower_corner (R : realType) (Q : set (R*R)) (x : R*R) :=
  Q x /\ forall y, Q y -> (x.1<=y.1 /\ x.2<=y.2)%R.

(** Source for [is_bohr_patch]: abstract finite-group
    specification supporting Federer 2.8.20, p. 152;
    Saks1934 Lemma B (4), (6), p. 258,
    and Cesari1939 Lemma III, p. 306. Its laws
    mention only sets, areas, and a positive common core. *)
Record is_bohr_patch (R : realType) (Q : set (R*R)) r
    (H K : 'I_r -> set (R*R)) (E : set (R*R)) : Prop := {
  (** Source for [bohr_patch_parent]: positive remaining region
      in the packing supporting Federer 2.8.20, p. 152. *)
  bohr_patch_parent : is_nondegenerate_half_open_rectangle Q;
  (** Source for [bohr_patch_size]: nonempty finite group in
      Saks1934 Lemma B, p. 258, supporting Federer 2.8.20. *)
  bohr_patch_size : (0<r)%N;
  (** Source for [bohr_patch_companions]: eligible closed cells
      and their auxiliary half-open companions in the construction
      supporting Federer 2.8.20, p. 152. *)
  bohr_patch_companions : forall i, are_rectangle_companions (H i) (K i);
  (** Source for [bohr_patch_inclusion]: local placement inside
      a remaining rectangle for Federer 2.8.20, p. 152;
      Saks1934 Lemma B, p. 258. *)
  bohr_patch_inclusion : forall i, H i `<=` Q;
  (** Source for [bohr_patch_anchor]: the rectangles of the
      fan share the lower corner in the placement supporting
      Federer 2.8.20, p. 152; Cesari1939 Lemma III,
      p. 306. This extra supporting law makes the
      family of small closed fan unions fine at that corner. *)
  bohr_patch_anchor : forall x, is_rectangle_lower_corner Q x -> forall i, K i x;
  (** Source for [bohr_patch_core]: positive common core in
      Saks1934 Lemma B (6), p. 258, supporting Federer
      2.8.20, p. 152. *)
  bohr_patch_core : is_nondegenerate_scalar_rectangle E;
  (** Source for [bohr_patch_core_inclusion]: the common-core
      inclusions supporting Federer 2.8.20, p. 152. *)
  bohr_patch_core_inclusion : forall i, E `<=` K i;
  (** Source for [bohr_patch_cell_area]: equal local cell areas
      in Saks1934 Lemma B (4), p. 258, supporting
      Federer 2.8.20, p. 152. *)
  bohr_patch_cell_area : forall i,
    scalar_plane_lebesgue (K i) = ((r%:R : R)^-1)%:E * scalar_plane_lebesgue Q;
  (** Source for [bohr_patch_area_gain]: the local harmonic
      area gain from Cesari1939 Lemma III, p. 306,
      supporting Federer 2.8.20, p. 152. *)
  bohr_patch_area_gain : (harmonic_partial_sum R r / r%:R)%:E * scalar_plane_lebesgue Q <=
    scalar_plane_lebesgue (\bigcup_(i in @setT 'I_r) H i)
}.
