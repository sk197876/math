(** Federer (1969), 3.4.5, p. 319: absorb
    the extra scalar in the factorial-growth bound into one
    analytic constant for all positive derivative orders. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_factorial_growth_majorant]: supporting
    realisation of the original growth classes in 3.4.5,
    p. 319. The bound S*T^m*m! is at most
    ((S+1)*(T+1))^m*m! for every positive integer m.
    The actual constant coefficient is handled separately. *)
Lemma analytic_factorial_growth_majorant (R:realType) (S T:R) m:
  0<=S ->0<=T ->(1<=m)%N ->
  S*T^+m*(m`!)%:R<=((S+1)*(T+1))^+m*(m`!)%:R.
Proof.
move=>hS hT hM.
have hStepS:S<=S+1 by rewrite lerDl ler01.
have hStepT:T<=T+1 by rewrite lerDl ler01.
have hOneS:1<=S+1 by rewrite addrC lerDl.
have hSMajor:=le_trans hStepS (ler_eXnr hM hOneS).
have hTPositive:0<=T+1:=addr_ge0 hT ler01.
have hTPower:=lerXn2r m hT hTPositive hStepT.
have hFirst:=ler_wpM2r (exprn_ge0 m hT) hSMajor.
have hSPositive:0<=S+1:=addr_ge0 hS ler01.
have hSecond:=ler_wpM2l (exprn_ge0 m hSPositive) hTPower.
have hPower:=le_trans hFirst hSecond.
rewrite -exprMn in hPower.
apply:ler_wpM2r;first exact:ler0n.
exact:hPower.
Qed.
