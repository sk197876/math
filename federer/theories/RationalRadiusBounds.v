(** Federer (1969), 3.1.3(1), pp. 212–213: a bound on the measure
    of all small sections can be tested on positive rational radii.
    Monotonicity of the sections and continuity of their polynomial
    volume bound suffice; continuity of the section mass is unnecessary. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology
  MeasurableRealPairs.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [monotone_rational_radius_bound]: the equality of the
    all-radius and rational-radius descriptions of T in Federer 3.1.3(1),
    p. 213. This supporting order argument allows any continuous real
    upper bound and any extended-real monotone mass function. *)
Theorem monotone_rational_radius_bound (R : realType)
    (F : R -> \bar R) (g : real_line_metric R -> real_line_metric R) d :
  (forall r s, (0<r)%R -> (r<=s)%R -> F r<=F s) ->
  continuous g ->
  (forall q : rat, (0<(ratr q : R))%R -> (ratr q<d)%R -> F (ratr q)<=(g (ratr q))%:E) ->
  forall r, (0<r)%R -> (r<d)%R -> F r<=(g r)%:E.
Proof.
move=> hmono hg hrat r hr hrd; rewrite leNgt; apply/negP=> hbad.
have [p [hgp hpF]] := @extended_rationals_order_dense R (g r)%:E (F r) hbad.
have hgap : (0<ratr p-g r)%R by rewrite subr_gt0; exact hgp.
have hn : nbhs (g r) [set z : real_line_metric R | (mdist (g r) z<ratr p-g r)%R].
  apply: (proj2 (metricType_numDomainType.nbhs_mdistP (g r) _)).
  exists (ratr p-g r)%R=> // z hz.
have [e he hball] := proj1 (metricType_numDomainType.nbhs_mdistP
  (r : real_line_metric R) _) (hg r _ hn).
pose h := (Num.min e (d-r)/2)%R.
have hmpos : (0<Num.min e (d-r))%R by rewrite lt_min subr_gt0; apply/andP; split.
have hh : (0<h)%R by rewrite /h; lra.
have hmine : (Num.min e (d-r)<=e)%R by rewrite ge_min lexx.
have hmind : (Num.min e (d-r)<=d-r)%R by rewrite ge_min lexx orbT.
have hhe : (h<=e/2)%R by rewrite /h; lra.
have hhd : (h<=(d-r)/2)%R by rewrite /h; lra.
have hrh : (r<r+h)%R by rewrite ltrDl.
have [q [hrq hqrh]] := @real_rationals_order_dense R r (r+h)%R hrh.
have hq0 : (0<(ratr q : R))%R := lt_trans hr hrq.
have hqd : (ratr q<d)%R by lra.
have hdist : (mdist (r : real_line_metric R) (ratr q : real_line_metric R)<e)%R.
  rewrite real_line_metric_distanceE distrC ger0_norm; lra.
have hnear := hball (ratr q) hdist.
change (is_true (`|g r-g (ratr q)|<ratr p-g r)%R) in hnear.
have hnorm := ler_norm (g (ratr q)-g r); rewrite distrC in hnorm.
have hgpq : (g (ratr q)<ratr p)%R by lra.
have hmass := le_trans (hmono _ _ hr (ltW hrq)) (hrat q hq0 hqd).
have hgpqE : (g (ratr q))%:E < (ratr p : R)%:E by rewrite lte_fin.
have hcontra := lt_trans hpF (le_lt_trans hmass hgpqE).
by rewrite ltxx in hcontra.
Qed.
