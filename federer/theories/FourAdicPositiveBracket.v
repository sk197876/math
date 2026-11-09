(** Federer (1969), 3.3.20, p. 308:
    the actual positive four-adic bracket for sigma. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import SequencePowerBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [four_adic_positive_bracket]: the choice
    of positive k with 2/4^(k+1)<sigma<=2/4^k
    in 3.3.20, p. 308. The proof uses
    actual geometric decay and a least positive crossing;
    no scale or logarithm is supplied as a premise. *)
Theorem four_adic_positive_bracket (R:realType) (sigma:R):
  0<sigma ->sigma<=1/2 ->exists k:nat,(1<=k)%N /\
    2/(4:R)^+k.+1<sigma /\sigma<=2/(4:R)^+k.
Proof.
move=>hSigma hHalf.
have hSmall:0<sigma/2 by lra.
have [N hN]:=@sequence_inverse_power_small R (sigma/2) hSmall.
have hInv0:0<=(4:R)^-1 by rewrite invr_ge0 ler0n.
have hInv:(4:R)^-1<=(2:R)^-1 by lra.
have hInv2:0<=(2:R)^-1 by rewrite invr_ge0 ler0n.
have hPower:((4:R)^-1)^+N<=((2:R)^-1)^+N:=lerXn2r N hInv0 hInv2 hInv.
have hCross:exists j:nat,2/(4:R)^+j<sigma.
  exists N;rewrite -exprVn;nra.
have [j hJ hMinimal]:=ex_minnP hCross.
have hJPositive:(0<j)%N.
  case:j hJ hMinimal=>[|j] hJ hMinimal;last by [].
  by rewrite expr0 divr1 in hJ;lra.
case:j hJ hMinimal hJPositive=>[//|k] hJ hMinimal hJPositive.
have hPrevious:~2/(4:R)^+k<sigma.
  move=>hBefore;have h:=hMinimal k hBefore.
  by have hFalse:=leq_ltn_trans h (ltnSn k);rewrite ltnn in hFalse.
have hUpper:sigma<=2/(4:R)^+k by rewrite leNgt;apply/negP;exact:hPrevious.
have hK:(1<=k)%N.
  rewrite lt0n;apply/eqP=>hKZero.
  have hJ0:=hJ;rewrite hKZero expr1 in hJ0.
  have hQuarter:2/(4:R)= 1/2 by field.
  rewrite hQuarter in hJ0.
  by have hFalse:=lt_le_trans hJ0 hHalf;rewrite ltxx in hFalse.

exists k;by split=>//;split.
Qed.
