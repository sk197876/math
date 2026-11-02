(** Federer (1969), 3.2.7, p. 246, third
    example: the signed square-root change of parameter.
    Specify its two scalar laws before constructing and
    hiding a witness; regularity is proved downstream. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_signed_square_root]: supporting scalar
    parameter for the oscillatory example of Federer
    3.2.7, p. 246. The two half-line laws
    agree at zero and uniquely specify the function. *)
Record is_signed_square_root (R:realType) (G:R->R):Prop:={
  (** Source for [signed_square_root_nonnegative]: the positive
      branch supporting the substitution example of Federer
      3.2.7, p. 246; this is a defining scalar law. *)
  signed_square_root_nonnegative:forall x,0<=x -> G x=Num.sqrt x;
  (** Source for [signed_square_root_nonpositive]: the negative
      branch supporting the substitution example of Federer
      3.2.7, p. 246; its sign agrees with x. *)
  signed_square_root_nonpositive:forall x,x<= 0 -> G x= -Num.sqrt (-x)
}.
