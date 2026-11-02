(** Federer (1969), 3.2.38, p. 275: a uniform
    finite coefficient absorbs all compact-core reciprocal errors. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [reciprocal_core_error_bound]: supporting the final
    vanishing-error display in Federer 3.2.38, p. 275.
    The compact-core variant has two bad-set errors. Their
    coefficients depend only on source mass and the fixed map
    and dimension constants, never on the radius or integer. *)
Lemma reciprocal_core_error_bound (R:realType) (t M xi eta V:R):
  0<=xi ->1<=V ->
  V^-1*t+M*V^-1+(xi/V)*(t+V^-1)+eta*(2*V^-1)<=
    (t+M+xi*(t+1)+2*eta)/V.
Proof.
move=>hXi hV.
have hPositive:0<V:=lt_le_trans ltr01 hV.
have hInverse:V^-1<=1 by rewrite invr_le1 ?unitfE ?(gt_eqF hPositive) //.
have hTerm:=ler_wpM2l hXi (lerD (lexx t) hInverse).
have hInv0:0<=V^-1 by rewrite invr_ge0; exact:ltW hPositive.
have hScaled:=ler_wpM2r hInv0 hTerm.
have hLeft:V^-1*t+M*V^-1+(xi/V)*(t+V^-1)+eta*(2*V^-1)=
    (t+M+2*eta)/V+(xi*(t+V^-1))/V by ring.
have hRight:(t+M+xi*(t+1)+2*eta)/V=
    (t+M+2*eta)/V+(xi*(t+1))/V by ring.
rewrite hLeft hRight; exact:lerD (lexx _) hScaled.
Qed.
