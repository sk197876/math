(** Federer (1969), 3.1.24, p. 239: the
    last scalar inequality in the composition norm estimate. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_composition_scalar_bound]: the inequality
    c^p gamma(gamma+1)^(p-1) <= [c(gamma+1)]^p in
    Federer 3.1.24, p. 239. Both parameters may
    be zero; positivity of the integer p is the only
    condition needed to extract its first outer factor. *)
Lemma analytic_composition_scalar_bound (R:realType) (c g:R) p :
  0<=c -> 0<=g -> (1<=p)%N ->
  c^+p*g*(g+1)^+(p-1)<=(c*(g+1))^+p.
Proof.
move=>hc hg hp.
have hg1:0<=g+1:=addr_ge0 hg ler01.
have hpe:p= (p-1).+1 by rewrite subn1 prednK.
have hpow:(g+1)^+p= (g+1)*(g+1)^+(p-1) by rewrite -exprS -hpe.
rewrite exprMn hpow -mulrA.
have hle:g<=g+1 by rewrite lerDl ler01.
have hmul:=ler_wpM2r (exprn_ge0 (p-1) hg1) hle.
exact (ler_wpM2l (exprn_ge0 p hc) hmul).
Qed.
