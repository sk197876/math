(** Federer (1969), 3.4.5, p. 321: actual
    coordinate lines in the adapted real cubic-surface
    proof of the cited example. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Coordinates.
Variable R:realType.
Local Notation X:=(R_n R 3).
Local Notation j:=(Ordinal (isT:(1<3)%N)).

(** Source for [cartan_axis_point]: the original
    z-axis point (0,0,z), supporting 3.4.5, p. 321. *)
Definition cartan_axis_point (z:R):X:=z*:(@coordinate_basis R 3 ord_max).

(** Source for [cartan_axis_point_coordinates]: the actual
    axis retains exactly its three original coordinates,
    supporting 3.4.5, p. 321. *)
Lemma cartan_axis_point_coordinates z:
  cartan_axis_point z ord0=0 /\cartan_axis_point z j=0 /\cartan_axis_point z ord_max=z.
Proof.
rewrite /cartan_axis_point /coordinate_basis !ffunE /=.
change (z*0=0 /\z*0=0 /\z*1=z).
by rewrite mulr0 mulr1.
Qed.

(** Source for [cartan_first_coordinate_line]: translation
    in the first coordinate retains the original two
    other coordinates, supporting 3.4.5, p. 321. *)
Lemma cartan_first_coordinate_line (v:X) t:
  (v+t*:(@coordinate_basis R 3 ord0)) ord0=v ord0+t /\
  (v+t*:(@coordinate_basis R 3 ord0)) j=v j /\
  (v+t*:(@coordinate_basis R 3 ord0)) ord_max=v ord_max.
Proof.
rewrite /coordinate_basis !ffunE /=.
change (v ord0+t*1=v ord0+t /\v j+t*0=v j /\v ord_max+t*0=v ord_max).
by rewrite mulr1 mulr0 !addr0.
Qed.

(** Source for [cartan_second_coordinate_line]: translation
    in the second coordinate retains the first and last
    original coordinates, supporting 3.4.5, p. 321. *)
Lemma cartan_second_coordinate_line (v:X) t:
  (v+t*:(@coordinate_basis R 3 j)) ord0=v ord0 /\
  (v+t*:(@coordinate_basis R 3 j)) j=v j+t /\
  (v+t*:(@coordinate_basis R 3 j)) ord_max=v ord_max.
Proof.
rewrite /coordinate_basis !ffunE /=.
change (v ord0+t*0=v ord0 /\v j+t*1=v j+t /\v ord_max+t*0=v ord_max).
by rewrite mulr1 mulr0 !addr0.
Qed.
End Coordinates.
