(** Federer (1969), 3.2.13, p. 250: positive
    dyadic interval covers used to prove finite Gamma mass.
    These local scalar choices serve existence proofs only. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra ring.
From Federer Require Import GeometricIntegerCells.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [gamma_origin_interval]: closed dyadic
    intervals for the near-zero bound of the defining
    Gamma integral, Federer 3.2.13, p. 250.
    Overlap at endpoints is harmless for an upper majorant. *)
Definition gamma_origin_interval (R:realType) n:set R:=
  [set x|(1/2)^+n/2<=x /\x<=(1/2)^+n].

(** Source for [gamma_tail_interval]: the positive
    dyadic tail intervals used for Gamma finiteness,
    Federer 3.2.13, p. 250. *)
Definition gamma_tail_interval (R:realType) n:set R:=
  [set x|2^+n<=x /\x<= 2^+n.+1].

(** Source for [gamma_tail_intervals_cover]: coverage
    of x>=1 in the tail bound for Gamma,
    Federer 3.2.13, p. 250, by the
    already proved geometric first-crossing principle. *)
Lemma gamma_tail_intervals_cover (R:realType) (x:R):
  1<=x ->exists n,@gamma_tail_interval R n x.
Proof.
move=>hx; have hTwo:(1:R)<2 by lra.
have [n [hn hNext]]:=geometric_natural_cell hTwo hx.
exists n; split=> //; exact:ltW hNext.
Qed.

(** Source for [gamma_origin_intervals_cover]: coverage
    of 0<x<=1 in the near-zero bound for
    Gamma, Federer 3.2.13, p. 250.
    No logarithmic floor or chosen integer is exported. *)
Lemma gamma_origin_intervals_cover (R:realType) (x:R):
  0<x ->x<=1 ->exists n,@gamma_origin_interval R n x.
Proof.
move=>hx hx1.
have hTwo:(1:R)<2 by lra.
have hTwo0:(0:R)<2 by lra.
have hInv:0<x^-1 by rewrite invr_gt0.
have hInv1:1<=x^-1.
  by rewrite -div1r ler_pdivlMr // mul1r.
have [n [hn hNext]]:=geometric_natural_cell hTwo hInv1.
have hPow0:(0:R)<2^+n:=exprn_gt0 n hTwo0.
have hPow1:(0:R)<2^+n.+1:=exprn_gt0 n.+1 hTwo0.
have hHalf:(1/2:R) = 2^-1 by rewrite mul1r.
have hUpper:x<=(2^+n)^-1.
  by rewrite -{1}(invrK x) lef_pV2 //.
have hLower:(2^+n.+1)^-1<=x.
  rewrite -{1}(invrK x) lef_pV2 //; exact:ltW hNext.
have hStep:((2:R)^+n.+1)^-1=(1/2)^+n/2.
  by rewrite exprS invfM hHalf exprVn mulrC.
exists n; split.
- by rewrite -hStep.
- by rewrite hHalf exprVn.
Qed.
