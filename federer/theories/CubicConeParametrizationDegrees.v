(** Federer (1969), 3.4.5, p. 321: finite
    degree arithmetic for restricting polynomials to the cubic
    cone in the example cited to Cartan (1957), pp. 97–99.
    This is internal support for the real Taylor argument. *)
From mathcomp Require Import all_boot all_order all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope nat_scope.

(** Source for [cubic_cone_remainder_degrees_injective]:
    the monomials x^i*y^j with i<3 have distinct
    degrees after x=1+t^2 and y=t*(1+t^2), supporting
    the cubic-cone polynomial argument in 3.4.5, p. 321. *)
Lemma cubic_cone_remainder_degrees_injective N:
  injective (fun p:('I_3*'I_N)%type=>2 * (p.1:nat)+3 * (p.2:nat)).
Proof.
move=>[i j] [k l] /= hDegree.
have hMod:=congr1 (fun n=>n%%3) hDegree.
have hLeft:(2 * (i:nat)+3 * (j:nat))%%3=(2 * (i:nat))%%3.
  by rewrite addnC [3 * (j:nat)]mulnC modnMDl.
have hRight:(2 * (k:nat)+3 * (l:nat))%%3=(2 * (k:nat))%%3.
  by rewrite addnC [3 * (l:nat)]mulnC modnMDl.
rewrite hLeft hRight in hMod.
have hSmall:forall a b:nat,a<3 ->b<3 ->(2 * a)%%3=(2 * b)%%3 ->a=b.
  by move=>[|[|[|a]]] [|[|[|b]]] //=.
have hI:i=k.
  apply:val_inj;exact:(hSmall (i:nat) (k:nat) (ltn_ord i) (ltn_ord k) hMod).
have hJ:j=l.
  apply:val_inj.
  rewrite hI in hDegree.
  have hThree:3 * (j:nat)=3 * (l:nat):=addnI hDegree.
  by move/eqP:hThree;rewrite eqn_mul2l /= =>/eqP.
by rewrite hI hJ.
Qed.
