(** Federer (1969), 3.4.6, p. 322: finite
    coefficient families can be indexed by natural numbers
    without changing their original finite entries. *)
From mathcomp Require Import all_boot all_order all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [weierstrass_finite_family_extension]: a
    local indexing witness for the original finite
    coefficient list, supporting 3.4.6(2), p. 322.
    Values outside the list are irrelevant, including
    when the original finite family is empty. *)
Theorem weierstrass_finite_family_extension (T:Type) k (F:'I_k->T) (d:T):
  exists f:nat->T,forall i:'I_k,f i=F i.
Proof.
exists (fun n=>nth d [seq F i | i<-enum 'I_k] n)=>i.
by rewrite (nth_map i) ?size_enum_ord ?ltn_ord // nth_ord_enum.
Qed.
