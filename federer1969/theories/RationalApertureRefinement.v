(** Federer (1969), 3.3.17, p. 300: rational apertures
    retain a strict normalized conical bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology lra.
From Federer Require Import RealMetricBackground PolynomialStrictNeighbourhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rational_aperture_refinement]: the choice
    0<t<s and lambda*s^m<mu*t^m with rational t in Federer
    3.3.17, p. 300. The actual polynomial continuity and rational
    order density prove existence, including degree zero. Neither
    aperture nor its normalization inequality is assumed supplied. *)
Lemma rational_aperture_refinement (R:realType) m (s lam mu:R):
  0<s ->lam<mu ->exists t:rat,(0<(ratr t:R)<s) /\lam*s^+m<mu*(ratr t:R)^+m.
Proof.
move=>hs hLamMu.
have hPower:0<s^+m:=exprn_gt0 m hs.
have hStrict:(-mu)*s^+m< -(lam*s^+m).
  by rewrite mulNr ltrN2 ltr_pM2r.
have [d [hd hLocal]]:=@polynomial_strict_upper_neighbourhood R (-mu) s (-(lam*s^+m)) m hStrict.
pose gap:=Num.min d s/2.
have hMin:0<Num.min d s by rewrite lt_min hd hs.
have hGap:0<gap by rewrite /gap divr_gt0 // ltr0n.
have hGapD:gap<d.
  have hHalf:gap<Num.min d s by rewrite /gap; lra.
  have hMinD:Num.min d s<=d by rewrite ge_min lexx.
  exact:lt_le_trans hHalf hMinD.
have hGapS:gap<s.
  have hHalf:gap<Num.min d s by rewrite /gap; lra.
  have hMinS:Num.min d s<=s by rewrite ge_min lexx orbT.
  exact:lt_le_trans hHalf hMinS.
have hInterval:s-gap<s by lra.
have [t /andP[hLow hHigh]]:=rat_in_itvoo hInterval.
have hT:0<(ratr t:R).
  have hLeft:0<s-gap by rewrite subr_gt0; exact:hGapS.
  exact:lt_trans hLeft hLow.
have hDistance:mdist (s:real_line_metric R) (ratr t)<d.
  change (is_true (`|s-ratr t|<d)).
  have hDifference:0<=s-ratr t by rewrite subr_ge0; exact:ltW hHigh.
  rewrite ger0_norm //.
  have hNear:s-ratr t<gap.
    have hBase:s<(ratr t:R)+gap by rewrite -ltrBlDr; exact:hLow.
    rewrite ltrBlDr [gap+(ratr t:R)]addrC; exact:hBase.
  exact:lt_trans hNear hGapD.
have hValue:=hLocal (ratr t) hDistance.
rewrite mulNr ltrN2 in hValue.
exists t; split; first by apply/andP; split.
exact:hValue.
Qed.
