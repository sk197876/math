(** Federer (1969), 4.1.15, p. 373: the elementary
    alternating scalar sequence in the final nonconvergence
    example. This supports both the origin slopes and the
    action on a detecting current test. *)
From mathcomp Require Import all_boot all_order all_algebra
  reals lra ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [nonzero_alternating_real_sequence_diverges]: the
    values (-1)^i b for b nonzero do not converge,
    supporting the final observation of 4.1.15, p. 373. *)
Theorem nonzero_alternating_real_sequence_diverges (R:realType) (b:R):
  b<>0 ->~exists c:R,forall eps:R,0<eps->exists N,forall i,(N<=i)%N->
    `|(-1:R)^+i*b-c|<eps.
Proof.
move=>hb [c hLimit].
have hbN:b!=0 by apply/negP=>/eqP;exact:hb.
have hB:0<`|b| by rewrite normr_gt0 hbN.
have hEpsilon:0<`|b|/2 by rewrite divr_gt0 // ltr0n.
have [N hN]:=hLimit (`|b|/2) hEpsilon.
have hEven:(N<=N+N)%N:=leq_addr N N.
have hOdd:(N<=(N+N).+1)%N:=leq_trans hEven (leqnSn (N+N)).
have hA:=hN (N+N)%N hEven.
have hBIndex:=hN (N+N).+1 hOdd.
have hEvenSign:(-1:R)^+(N+N)= 1.
  by rewrite -signr_odd oddD addbb expr0.
have hOddSign:(-1:R)^+(N+N).+1= -1.
  by rewrite exprS hEvenSign mulr1.
rewrite hEvenSign mul1r in hA.
rewrite hOddSign mulN1r in hBIndex.
have hTriangle:=ler_normD (b-c) (c-(-b)).
have hSum:(b-c)+(c-(-b))= 2*b by ring.
have hOpp:c-(-b)= -(-b-c) by ring.
rewrite hSum hOpp normrN normrM (ger0_norm (ler0n R 2)) in hTriangle.
nra.
Qed.
