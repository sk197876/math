(** Federer (1969), 3.4.8(8), p. 329:
    the canonical quotient O_0(R^n)/I_g is
    specified by its surjection and exact original
    kernel. These independent laws precede existence
    and the private quotient representation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_commutative_ideal_quotient]: the original
    canonical ring homomorphism p and quotient
    by I_g in 3.4.8(8), p. 329.
    Surjectivity and the exact kernel determine
    its usual universal property. No integral
    extension or field conclusion is assumed. *)
Record is_commutative_ideal_quotient (A C:comNzRingType) (I:set A)
  (projection:{rmorphism A->C}):Prop:={
  (** Source for [commutative_quotient_surjective]: every
      quotient class has an original germ
      representative, 3.4.8(8), p. 329. *)
  commutative_quotient_surjective:forall y:C,exists x:A,projection x = y;
  (** Source for [commutative_quotient_kernel]: the original
      kernel of p is exactly I_g,
      3.4.8(8), p. 329. *)
  commutative_quotient_kernel:forall x:A,projection x = 0 <->I x
}.
