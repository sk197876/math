(** Federer (1969), 3.4.12, p. 339, extending 3.4.5,
    p. 319: the original holomorphic germ ring is covered
    by its positive-integer factorial-growth classes. Reuse the
    proved actual jet growth and Archimedean integer bounds. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  HolomorphicGermUP HolomorphicGermGrowthUP HolomorphicGermGrowthSealed HolomorphicGermJetGrowth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [holomorphic_germ_positive_growth_cover]: every original
    germ belongs to a class with positive integer indices,
    extending 3.4.5, p. 319. Degree zero is retained. *)
Theorem holomorphic_germ_positive_growth_cover (R:realType)
    (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:is_complex_norm NX) a
    (alpha:holomorphic_germ_space (complex_norm_real hNX) a):
  exists s t:nat,(1<=s)%N /\(1<=t)%N /\
    @HolomorphicGermGrowth.value R X NX (complex_norm_real hNX) a s t alpha.
Proof.
have [b [c [hb [hc hGrowth]]]]:=@holomorphic_germ_positive_jet_growth R X NX hNX a alpha.
pose s:=(Num.bound b).+1.
pose t:=(Num.bound c).+1.
have hB:b<=s%:R.
  apply:le_trans (ltW (archi_boundP (ltW hb))) _.
  by rewrite /s ler_nat leqnSn.
have hC:c<=t%:R.
  apply:le_trans (ltW (archi_boundP (ltW hc))) _.
  by rewrite /t ler_nat leqnSn.
exists s,t;split;first by rewrite /s.
split;first by rewrite /t.
apply/(@holomorphic_germ_growth_membership R X NX (complex_norm_real hNX) a s t _
  (@HolomorphicGermGrowth.laws R X NX (complex_norm_real hNX) a s t) alpha)=>m.
apply:le_trans (hGrowth m) _.
apply:ler_wpM2r;first exact:ler0n.
exact:ler_pM (ltW hb) (exprn_ge0 m (ltW hc)) hB (lerXn2r m (ltW hc) (ler0n R t) hC).
Qed.
