(** Federer (1969), 3.4.4, p. 318: supporting
    finite coordinates for the original left/right interval addresses. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [binary_cantor_address_coordinates_exists]:
    the two endpoint positions underlying the original order
    correspondence in 3.4.4, p. 318. A finite-word
    recursion is an existence witness for the independent root,
    first-digit, and appended-digit equations. The address function
    remains local to this existence proof. *)
Theorem binary_cantor_address_coordinates_exists (R:realType) (rho:R):
  exists a:seq bool->R,a [::]=0 /\
    (forall b w,a (b::w)=(if b then 1-rho else 0)+rho*a w) /\
    forall w b,a (rcons w b)=a w+(if b then 1-rho else 0)*rho^+(size w).
Proof.
pose a:=fix build (w:seq bool):R:=
  if w is b::v then (if b then 1-rho else 0)+rho*build v else 0.
exists a;split;first by [].
split;first by move=>b w.
elim=>[|c w ih] b.
- by rewrite /a /= expr0 mulr1 add0r mulr0 addr0.
- change ((if c then 1-rho else 0)+rho*a (rcons w b)=
    ((if c then 1-rho else 0)+rho*a w)+(if b then 1-rho else 0)*rho^+(size w).+1).
  rewrite ih exprS;ring.
Qed.
