(** Federer (1969), 3.3.20, pp. 308–309:
    actual reflected original addresses at opposite corners. *)
From mathcomp Require Import all_boot.
From Federer Require Import CriticalCantorAddressUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [critical_cantor_opposite_address]: each
    original address a at level j has an actual
    original opposite address b with a+b+1=4^j.
    Complementing only the original endpoint-child digits
    proves the reflection used by the four corner
    certificates in 3.3.20, pp. 308–309. No
    reflected set is assumed to be the original set. *)
Lemma critical_cantor_opposite_address j a:critical_cantor_address j a ->
  exists b,critical_cantor_address j b /\(a+b+1=4^j)%N.
Proof.
move=>hAddress;elim:hAddress=>[|k u d hA [v [hV hSum]] /orP[/eqP->|/eqP->]].
- exists 0;split;first exact:critical_cantor_address_root.
  by [].
- exists (4 * v+3);split.
  + exact:(@critical_cantor_address_step k v 3 hV (erefl true)).
  + rewrite expnS -hSum mulnDr mulnDr muln1 addn0.
    by rewrite -!addnA.
- exists (4 * v+0);split.
  + exact:(@critical_cantor_address_step k v 0 hV (erefl true)).
  + rewrite expnS -hSum mulnDr mulnDr muln1 addn0.
    by rewrite (addnAC (4 * u) 3 (4 * v)) -!addnA.
Qed.
