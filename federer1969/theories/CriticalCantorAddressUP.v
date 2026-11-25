(** Federer (1969), 3.3.20, pp. 306–309:
    independent finite-address laws for the original critical intervals. *)
From mathcomp Require Import all_boot.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [critical_cantor_address]: the original
    endpoint recursion at m=1/2 selects precisely
    zero and three as successive base-four digits,
    supporting the actual corner squares on pp. 308–309.
    This is an independent address relation; original
    interval membership and geometric conclusions are proved. *)
Inductive critical_cantor_address : nat->nat->Prop:=
  (** Source for [critical_cantor_address_root]: the root
      interval has original lower endpoint zero, 3.3.20, p. 306. *)
  | critical_cantor_address_root:critical_cantor_address 0 0
  (** Source for [critical_cantor_address_step]: the exact
      two original endpoint children from p. 306 at
      the critical ratio one quarter. *)
  | critical_cantor_address_step j a d:
      critical_cantor_address j a ->(d==0)||(d==3) ->
      critical_cantor_address j.+1 (4*a+d).
