(** Federer (1969), 3.2.33, p. 270: absorb finitely
    many early derivatives into the normal-convergence bound for
    the printed smooth scalar series. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [eventual_geometric_domination]: supporting uniform
    differentiated-series convergence in Federer 3.2.33, p. 270.
    A geometric estimate after a fixed index extends to all
    terms by a larger finite coefficient. This is elementary
    finite-sum algebra, not an assumed convergence theorem. *)
Lemma eventual_geometric_domination (R:realType) (b:nat->R) (q C:R) N:
  0<q ->0<=C ->(forall j,(N<=j)%N ->b j<=q^+j*C) ->
  exists M:R,0<M /\forall j,b j<=q^+j*M.
Proof.
move=>hq hC hTail.
pose B:R:=\sum_(j<N) `|b j/(q^+j)|.
have hB:0<=B by apply:sumr_ge0=>j _; exact:normr_ge0.
have hTerm j (hj:(j<N)%N):`|b j/(q^+j)|<=B.
  rewrite /B (bigD1 (Ordinal hj)) //= lerDl.
  apply:sumr_ge0=>k _; exact:normr_ge0.
exists (1+C+B); split; first by lra.
move=>j; have hPower:0<q^+j:=exprn_gt0 j hq.
have [hj|hj]:=leqP N j.
- apply:le_trans (hTail j hj) _.
  apply:ler_wpM2l; first exact:ltW hPower; by lra.
- rewrite mulrC -ler_pdivrMr //.
  have hRatio:=ler_norm (b j/(q^+j)).
  have hSmall:=hTerm j hj; lra.
Qed.
