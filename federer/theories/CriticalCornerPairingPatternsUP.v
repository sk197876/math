(** Federer (1969), 3.3.20, pp. 308–309:
    independent finite offset laws for the four
    original opposite-corner square-pairing certificates. *)
From mathcomp Require Import all_boot.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_critical_corner_pairing_pattern]: finite
    offset specification supporting the 16, 40, 28
    and 20 actual squares in 3.3.20, pp. 308–309.
    Offsets have base-four digits zero or three in
    their last two places. Reversal pairs opposite corners.
    The integer coordinate budget is independent of any
    distance, missing-count or Hausdorff conclusion. *)
Definition is_critical_corner_pairing_pattern (n budget:nat)
    (L:seq (nat*nat)):Prop:=
  size L=n /\uniq L /\
  all (fun p=>(p.1 \in [::0;3;12;15])&&(p.2 \in [::0;3;12;15])) L /\
  all (fun p=>(p.1.1+p.1.2+p.2.1+p.2.2<=budget)%N) (zip L (rev L)).
