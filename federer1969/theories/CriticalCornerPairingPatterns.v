(** Federer (1969), 3.3.20, pp. 308–309:
    proved local finite witnesses for the printed
    opposite-corner pairing arguments. No global list is selected. *)
From mathcomp Require Import all_boot.
From Federer Require Import CriticalCornerPairingPatternsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [critical_corner_four_offsets_exist]: the
    16-square certificate on p. 308: four squares
    per corner, eight opposite-corner pairs, total inward
    coordinate budget six and distance sqrt(2)(1-5/4^j). *)
Lemma critical_corner_four_offsets_exist:
  exists L,is_critical_corner_pairing_pattern 4 6 L /\
    all (fun p=>(p.1<=3)&&(p.2<=3)) L.
Proof.
exists [::(0,0);(0,3);(3,0);(3,3)].
by vm_compute.
Qed.

(** Source for [critical_corner_ten_offsets_exist]: the
    40-square certificate on pp. 308–309: ten
    squares per corner, twenty opposite-corner pairs,
    coordinate budget 24 and distance sqrt(2)(1-14/4^j). *)
Lemma critical_corner_ten_offsets_exist:
  exists L,is_critical_corner_pairing_pattern 10 24 L.
Proof.
exists [::(0,0);(0,3);(3,0);(3,3);(0,12);(12,0);(3,12);(12,3);(0,15);(15,0)].
by vm_compute.
Qed.

(** Source for [critical_corner_seven_offsets_exist]: the
    28-square certificate on p. 309: seven
    squares per corner, fourteen opposite-corner pairs,
    budget 15 and distance sqrt(2)(1-(19/2)/4^j). *)
Lemma critical_corner_seven_offsets_exist:
  exists L,is_critical_corner_pairing_pattern 7 15 L.
Proof.
exists [::(0,0);(0,3);(3,0);(3,3);(0,12);(12,0);(3,12)].
by vm_compute.
Qed.

(** Source for [critical_corner_five_offsets_exist]: the
    final 20-square certificate on p. 309:
    five squares per corner, ten opposite-corner pairs,
    budget 12 and distance sqrt(2)(1-8/4^j). *)
Lemma critical_corner_five_offsets_exist:
  exists L,is_critical_corner_pairing_pattern 5 12 L.
Proof.
exists [::(0,0);(0,3);(3,0);(3,3);(0,12)].
by vm_compute.
Qed.
