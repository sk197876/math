(** Federer (1969), 3.1.24, p. 240: supporting
    analytic addition and scalar multiplication in the quadratic
    expression for the inverse majorant. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_positive_power_sum_bound]: supporting
    the analytic sum in the scalar inverse expression,
    Federer 3.1.24, p. 240. For nonnegative c,d
    and positive m, c^m+d^m <= (c+d)^m. The
    elementary induction retains zero parameters. *)
Lemma analytic_positive_power_sum_bound (R:realType) (c d:R) m :
  0<=c -> 0<=d -> (1<=m)%N -> c^+m+d^+m<=(c+d)^+m.
Proof.
move=>hc hd; case:m=>[|m] hm; first by [].
clear hm.
elim:m=>[|m ih]; first by rewrite !expr1.
rewrite [c^+m.+2]exprS [d^+m.+2]exprS [(c+d)^+m.+2]exprS.
have hcross:0<=c*d^+m.+1+d*c^+m.+1.
  exact (addr_ge0 (mulr_ge0 hc (exprn_ge0 m.+1 hd)) (mulr_ge0 hd (exprn_ge0 m.+1 hc))).
have h1:c*c^+m.+1+d*d^+m.+1<=(c+d)*(c^+m.+1+d^+m.+1) by nra.
exact (le_trans h1 (ler_wpM2l (addr_ge0 hc hd) ih)).
Qed.

(** Source for [analytic_scalar_factor_bound]: supporting the
    constant scalar factors in the quadratic inverse expression
    of Federer 3.1.24, p. 240. A fixed nonnegative
    prefactor b is absorbed in the mth power of b+1
    for every positive order m. *)
Lemma analytic_scalar_factor_bound (R:realType) (b c:R) m :
  0<=b -> 0<=c -> (1<=m)%N -> b*c^+m<=((b+1)*c)^+m.
Proof.
move=>hb hc hm.
have hb1:1<=b+1 by rewrite lerDr.
have hbb:b<=b+1 by rewrite lerDl ler01.
have hpow:b<=(b+1)^+m:=le_trans hbb (ler_eXnr hm hb1).
rewrite exprMn; exact (ler_wpM2r (exprn_ge0 m hc) hpow).
Qed.
