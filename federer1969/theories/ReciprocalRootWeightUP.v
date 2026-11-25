(** Federer (1969), 3.2.7, p. 246:
    the printed cutoff weight |y|^(-1/2) on
    0<|y|<= 1. Specify its values abstractly; set
    the unspecified single value g(0) to zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_reciprocal_root_weight]: the
    weight in the third counterexample of Federer
    3.2.7, p. 246. The negative one-half
    power is the inverse positive square root.
    Completing g(0)= 0 is a null-point convention. *)
Record is_reciprocal_root_weight (R:realType) (g:R->R):Prop:={
  (** Source for [reciprocal_root_weight_on]: the
      printed nonzero unit-range values in Federer
      3.2.7, p. 246. *)
  reciprocal_root_weight_on:forall y,0<`|y| -> `|y|<= 1 -> g y=(Num.sqrt `|y|)^-1;
  (** Source for [reciprocal_root_weight_off]: the
      printed zero values outside the unit range in
      Federer 3.2.7, p. 246, with g(0)= 0
      completing the omitted single source value. *)
  reciprocal_root_weight_off:forall y,~(0<`|y| /\ `|y|<= 1) -> g y= 0
}.

(** Source for [reciprocal_root_weight_exists]: actual
    existence witness for the prescribed weight in
    Federer 3.2.7, p. 246. The function
    is specified before its case-based witness. *)
Theorem reciprocal_root_weight_exists (R:realType):
  exists g:R->R,is_reciprocal_root_weight g.
Proof.
exists (fun y=>if (0<`|y|)&&(`|y|<= 1) then (Num.sqrt `|y|)^-1 else 0); constructor.
- move=>y h0 h1; by rewrite h0 h1.
- move=>y hNot; have hb:((0<`|y|)&&(`|y|<= 1))=false.
    apply/negbTE/negP=>/andP[hy0 hy1]; exact (hNot (conj hy0 hy1)).
  by rewrite hb.
Qed.
