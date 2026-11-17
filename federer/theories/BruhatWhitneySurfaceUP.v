(** Federer (1969), 3.4.10, p. 338, citing
    Bruhat and Whitney (1959), section 11(c),
    p. 159: Cartan's polynomial surface.
    Its equation is specified independently of
    any regularity or counterexample assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import GrassmannAbbreviations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_bruhat_whitney_surface]: the
    actual equation yz(x^2-zy^2)+x^4=0,
    Bruhat and Whitney, section 11(c), p. 159,
    cited in 3.4.10, p. 338.
    No singular-locus description is assumed. *)
Record is_bruhat_whitney_surface (R:realType) (S:set (R_n R 3)):Prop:={
  (** Source for [bruhat_whitney_surface_membership]: the
      original polynomial membership equation, section 11(c),
      p. 159, supporting the example in
      3.4.10, p. 338. *)
  bruhat_whitney_surface_membership:forall v,S v <->
    v (Ordinal (isT:(1<3)%N))*v ord_max*
      ((v ord0)^+2-v ord_max*(v (Ordinal (isT:(1<3)%N)))^+2)+(v ord0)^+4=0
}.
