(** Federer (1969), 3.2.33, p. 270: independent coordinate
    laws for f(x)=(x_1,...,x_mu,g(x_(mu+1))). Source dimension
    (mu+1)+k represents every m>mu, including k= 0 and mu= 0. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import GrassmannAbbreviations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_scalar_cylinder_map]: the displayed definition
    of f in Federer 3.2.33, p. 270. The first mu
    coordinates are unchanged and the next is g of the next
    source coordinate. These laws select no implementation or
    global witness; their existence is proved separately. *)
Record is_scalar_cylinder_map (R:realType) mu k (g:R->R)
    (F:R_n R ((mu+1)+k)->R_n R (mu+1)):Prop:={
  (** Source for [scalar_cylinder_first_coordinates]: the first
      mu coordinates of f, Federer 3.2.33, p. 270. *)
  scalar_cylinder_first_coordinates:forall x i,
    F x (lshift 1 i)=x (lshift k (lshift 1 i));
  (** Source for [scalar_cylinder_last_coordinate]: the final
      coordinate g(x_(mu+1)), including mu= 0,
      Federer 3.2.33, p. 270. *)
  scalar_cylinder_last_coordinate:forall x,
    F x (rshift mu ord0)=g (x (lshift k (rshift mu ord0)))
}.
