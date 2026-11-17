(** Federer (1969), 3.4.12, p. 339: original holomorphic
    germs retain the factorial derivative growth of 3.4.5,
    p. 319. Reuse the defining real analytic bounds and local
    differential restriction; no complex convergence is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexModulus ComplexScalarNorm ContinuousMultilinearUP ContinuousMultilinearSealed
  NormHigherDifferentialUP NormHigherDifferentialLocal NormRegularity NormAnalyticUP NormAnalyticBoundNonnegative
  HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRingLaws HolomorphicGermJetsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Growth.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable hNX:is_complex_norm NX.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation NC:=(@complex_modulus R).
Local Notation hNC:=(@complex_modulus_real_norm R).
Local Notation Z:=(fun k=>@ContinuousMultilinear.space R k XR CR NX NC hNXR hNC).
Local Notation ev:=(fun k=>@ContinuousMultilinear.evaluation R k XR CR NX NC hNXR hNC).
Local Notation ZN:=(fun k=>@ContinuousMultilinear.norm R k XR CR NX NC hNXR hNC).
Local Notation hZ:=(fun k=>@ContinuousMultilinear.laws R k XR CR NX NC hNXR hNC).

(** Source for [holomorphic_germ_positive_jet_growth]: every actual
    original complex germ has one positive factorial majorant in
    every order, including zero, 3.4.12, p. 339, extending
    the growth-class cover of 3.4.5, p. 319. *)
Theorem holomorphic_germ_positive_jet_growth a (alpha:holomorphic_germ_space hNXR a):
  exists b c:R,0<b /\0<c /\forall m,
    @ZN m (@HolomorphicGermJets.value R X NX hNXR a m alpha)<=b*c^+m*(m`!)%:R.
Proof.
have [f hf]:=@holomorphic_germ_has_representative R X NX hNXR a alpha.
have [A [ha [hAnalytic _]]]:=holomorphic_representative_holomorphic f.
have [U [d [haU [hUA [hClass hBound]]]]]:=hAnalytic a ha.
have hd:=norm_analytic_operator_witness_nonnegative haU hClass hBound.
pose b:=@ZN 0%N (@HolomorphicGermJets.value R X NX hNXR a 0 alpha)+1.
pose c:=d+1.
have hbOne:1<=b.
  have hZero:=multilinear_operator_nonnegative
    (continuous_multilinear_norm_laws (hZ 0%N) (@HolomorphicGermJets.value R X NX hNXR a 0 alpha)).
  have hSum:=lerD hZero (lexx (1:R));by rewrite add0r in hSum.
have hb:0<b:=lt_le_trans ltr01 hbOne.
have hc:0<c.
  have hSum:=lerD hd (lexx (1:R));rewrite add0r in hSum.
  exact:lt_le_trans ltr01 hSum.
exists b,c;split;first exact:hb.
split;first exact:hc.
move=>[|m].
- rewrite expr0 mulr1 /= mulr1.
  have hSum:=lerD (lexx (@ZN 0%N (@HolomorphicGermJets.value R X NX hNXR a 0 alpha))) (@ler01 R).
  by rewrite addr0 in hSum.
- have hOpen x (hx:U x):@NormDifferentialUP.norm_domain_interior R XR NX U x:=((hClass 0%N).1 x hx).1.
  pose z:=@HolomorphicGermJets.value R X NX hNXR a m.+1 alpha.
  have hFull:=@HolomorphicGermJets.laws R X NX hNXR a m.+1 alpha f hf.
  have hLocal:=(@norm_higher_differential_open_restriction R XR CR NX NC hNXR hNC
    Z ev ZN hZ m.+1 setT U (holomorphic_representative_value f)
    (fun x _=>Logic.I) hOpen a haU z).1 hFull.
  have hOriginal:=hBound m.+1 (leq0n m) a haU z hLocal.
  have hDC:d<=c.
    have hSum:=lerD (lexx d) (@ler01 R);by rewrite addr0 in hSum.
  have hPower:=lerXn2r m.+1 hd (ltW hc) hDC.
  have hFact:0<=(((m.+1)`!)%:R:R) by rewrite ler0n.
  have hFirst:=le_trans hOriginal (ler_wpM2r hFact hPower).
  have hNonnegative:0<=c^+m.+1*(((m.+1)`!)%:R:R).
    exact:mulr_ge0 (exprn_ge0 _ (ltW hc)) hFact.
  have hLast:=ler_wpM2r hNonnegative hbOne.
  rewrite mul1r mulrA in hLast;exact:le_trans hFirst hLast.
Qed.
End Growth.
