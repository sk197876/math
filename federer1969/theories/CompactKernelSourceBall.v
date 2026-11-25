(** Federer (1969), 4.1.2, p. 347: one
    compact source ball suffices for nearby convolution
    centres. This is the geometric support estimate
    in differentiation under the original integral. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_kernel_source_ball_shift]: if z
    lies beyond the radius-r+1 source ball and the
    centre moves by less than one, both kernel
    arguments lie beyond radius r, supporting Federer
    4.1.2, p. 347. *)
Lemma norm_kernel_source_ball_shift (R:realType) (X:lmodType R)
    (N:X->R) (hN:is_real_norm N) (a h z:X) (r:R):
  N h<1 ->r+1<N (z-a) ->
  r<N (a-z) /\ r<N (a+h-z).
Proof.
move=>hSmall hOutside.
have hTriangle:=real_seminorm_triangle hN.1 (z-(a+h)) h.
have hSum:z-(a+h)+h=z-a by rewrite opprD addrA subrK.
rewrite hSum (real_seminorm_subtract hN.1 z (a+h)) in hTriangle.
rewrite (real_seminorm_subtract hN.1 a z).
split; lra.
Qed.
