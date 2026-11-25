(** An abstract finite-fan specification supporting the Bohr construction
    cited by Federer (1969), 2.8.20, p. 152. Saks1934 Lemma B, pp. 258–259,
    describes groups of equal-area rectangles with a positive common core
    and much larger union area. Cesari1939 Lemma III, p. 306, chooses the
    number of fan members using a large harmonic partial sum. The predicate
    below isolates one such group in a unit coordinate square. Its existence
    construction will remain private. Source titles:
    VitaliMassObstruction.v. These auxiliary laws are not claimed as a
    separate Federer statement *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ScalarPlaneRectangles HarmonicPrefixBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_bohr_fan]: supporting specification for
    the finite rectangular group used in Federer 2.8.20,
    p. 152; Saks1934 Lemma B, pp. 258–259, and
    Cesari1939 Lemma III, p. 306. The unit-square
    normalization will be transported to smaller rectangles
    only after this specification is proved to have a witness. *)
Record is_bohr_fan (R : realType) (r : nat) (F : 'I_r -> set (R*R))
    (E : set (R*R)) : Prop := {
  (** Source for [bohr_fan_positive_size]: a nonempty finite
      group in the construction supporting Federer 2.8.20,
      p. 152; Saks1934 Lemma B, p. 258. *)
  bohr_fan_positive_size : (0 < r)%N;
  (** Source for [bohr_fan_rectangles]: compact nondegenerate
      eligible rectangles in a normalized square, supporting
      Federer 2.8.20, p. 152. *)
  bohr_fan_rectangles : forall i, is_nondegenerate_scalar_rectangle (F i) /\
    F i `<=` scalar_closed_rectangle (0 : R) 1 0 1;
  (** Source for [bohr_fan_equal_area]: equal rectangle areas
      within a group in Saks1934 (4), p. 258, supporting
      Federer 2.8.20, p. 152. The normalization here
      sets each member's area to the reciprocal of r. *)
  bohr_fan_equal_area : forall i, scalar_plane_lebesgue (F i) = ((r%:R : R)^-1)%:E;
  (** Source for [bohr_fan_core_rectangle]: a positive-area
      common rectangular core, as in Saks1934 (6), p. 258,
      supporting Federer 2.8.20, p. 152. *)
  bohr_fan_core_rectangle : is_nondegenerate_scalar_rectangle E;
  (** Source for [bohr_fan_core_inclusion]: the common-core
      inclusion in Saks1934 (6), p. 258, supporting
      Federer 2.8.20, p. 152. *)
  bohr_fan_core_inclusion : forall i, E `<=` F i;
  (** Source for [bohr_fan_harmonic_gain]: the harmonic gain
      underlying the parameter choice in Cesari1939 Lemma III,
      p. 306, supporting Federer 2.8.20, p. 152.
      A sum of disjoint strips proves this lower bound. *)
  bohr_fan_harmonic_gain : (harmonic_partial_sum R r / r%:R)%:E <=
    scalar_plane_lebesgue (\bigcup_(i in @setT 'I_r) F i)
}.
