(** Federer (1969), 3.2.6, p. 246: a regular
    preimage crosses its level in the direction specified
    by the sign of f'. This is the local analytic step
    in the finite signed-fibre count. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra.
From Federer Require Import RealCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_derivative_regular_crossing_sign]:
    the observation about positive and negative derivatives
    in the proof of Federer 3.2.6, p. 246.
    On each sufficiently small punctured increment, the
    level displacement has the sign of h times f'(a). *)
Theorem real_derivative_regular_crossing_sign (R:realType) (f:R->R) (a v:R):
  has_real_curve_derivative f a v -> v!=0 ->
  exists d:R,0<d /\ forall h:R,0<`|h|<d ->
    Num.sg (f (a+h)-f a)=Num.sg h*Num.sg v.
Proof.
move=>hf hv.
have hvAbs:0<`|v| by rewrite normr_gt0.
have he:0<`|v|/2 by rewrite divr_gt0 // ltr0n.
have [d [hd hb]]:=hf (`|v|/2) he.
exists d; split=>// h hh.
have hn:h!=0 by have:= (andP hh).1; rewrite normr_gt0.
pose q:=(f (a+h)-f a)/h.
have hErr:`|q-v|<`|v|/2:=hb h hh.
have hUpper:q-v<=`|q-v| :=ler_norm (q-v).
have hLower:v-q<=`|q-v| by rewrite distrC; exact:ler_norm.
have hSign:Num.sg q=Num.sg v.
  case:(ltP 0 v)=>hvPos.
  - have hq:0<q by rewrite (ger0_norm (ltW hvPos)) in hErr; lra.
    by rewrite (gtr0_sg hq) (gtr0_sg hvPos).
  - have hvNeg:v<0 by rewrite lt_neqAle hv hvPos.
    have hq:q<0 by rewrite (ler0_norm (ltW hvNeg)) in hErr; lra.
    by rewrite (ltr0_sg hq) (ltr0_sg hvNeg).
have hId:f (a+h)-f a=q*h by rewrite /q divfK.
by rewrite hId sgrM hSign mulrC.
Qed.
