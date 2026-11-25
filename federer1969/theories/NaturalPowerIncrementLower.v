(** Federer (1969), 3.2.42, printed p. 278, first
    proof display: keep the constant and linear terms in the
    positive integer power of a sum. This elementary scalar
    induction also retains zero bases and zero increments. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [natural_power_increment_linear_lower]: supporting
    second inequality of the first display in the proof of
    Federer 3.2.42, p. 278. For n=k+1, nonnegative x,y,
    the power (x+y)^n is at least x^n+n*x^(n-1)*y.
    The scalar induction proves the omitted higher terms
    nonnegative rather than assuming convexity of powers. *)
Lemma natural_power_increment_linear_lower (R:realType) (x y:R) k:
  0<=x ->0<=y ->x^+k.+1+(k.+1)%:R*x^+k*y<=(x+y)^+k.+1.
Proof.
move=> hx hy; elim:k=>[|k ih].
- by rewrite !expr1 expr0 mulr1 mul1r.
- have hxy:0<=x+y:=addr_ge0 hx hy.
  have hMultiply:=ler_wpM2r hxy ih.
  rewrite -exprSr in hMultiply.
  have hExpansion:
      (x^+k.+1+(k.+1)%:R*x^+k*y)*(x+y)=
      x^+k.+2+(k.+2)%:R*x^+k.+1*y+(k.+1)%:R*x^+k*y^+2.
    have hSucc:((k.+2)%:R:R)=(k.+1)%:R+1 by rewrite -[k.+2]addn1 natrD.
    rewrite !exprS hSucc; ring.
  have hRemainder:0<=(k.+1)%:R*x^+k*y^+2.
    apply:mulr_ge0; last exact:exprn_ge0 _ hy.
    apply:mulr_ge0; [exact:ler0n|exact:exprn_ge0 _ hx].
  apply:le_trans _ hMultiply.
  rewrite hExpansion.
  by rewrite lerDl.
Qed.
