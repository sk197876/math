(** Federer (1969), 3.4.5, p. 321: in a
    finite polynomial relation in a small flat coefficient,
    the constant analytic coefficient is bounded by that
    flat coefficient. This is an internal finite estimate
    for the cited local/global example. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [flat_polynomial_constant_bound]: the actual
    finite estimate used before invoking analytic flatness,
    supporting the example cited in 3.4.5, p. 321.
    No independence or non-globality conclusion is assumed. *)
Lemma flat_polynomial_constant_bound (R:realType) N (a:nat->R) (p C:R):
  0<=p ->p<=1 ->0<=C ->
  (forall j,(j<N)%N ->`|a j.+1|<=C) ->
  (\sum_(i<N.+1) a i* p^+i)=0 ->`|a 0%N|<=N%:R*C* p.
Proof.
move=>hp hpOne hC hBound hSum.
rewrite big_ord_recl /= expr0 mulr1 in hSum.
pose tail:R:=\sum_(j<N) a (val j).+1* p^+(val j).+1.
have hEquation:a 0%N= -tail.
  apply/eqP;rewrite -addr_eq0;apply/eqP;exact:hSum.
rewrite hEquation normrN /tail.
apply:le_trans (real_seminorm_sum (@scalar_absolute_value_norm R).1
  (fun j:'I_N=>a (val j).+1* p^+(val j).+1)) _.
have hTerm (j:'I_N):`|a (val j).+1* p^+(val j).+1|<=C* p.
  rewrite normrM (ger0_norm (exprn_ge0 _ hp)).
  have hPower:p^+(val j).+1<=p.
    have hh:=ler_wpM2l hp (exprn_ile1 (val j) hp hpOne).
    by rewrite mulr1 -exprS in hh.
  exact:ler_pM (normr_ge0 _) (exprn_ge0 _ hp) (hBound j (valP j)) hPower.
have hEstimate:(\sum_(j<N) `|a (val j).+1* p^+(val j).+1|)<=\sum_(j<N) C* p.
  apply:ler_sum=>j _;exact:hTerm.
apply:le_trans hEstimate _.
by rewrite sumr_const card_ord -[C* p*+N]mulr_natl mulrA.
Qed.
