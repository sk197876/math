(** Federer (1969), 2.9.24, p. 169: only the variation of f on [a,b] is
    assumed finite. Composition with the segment retraction gives a proof
    representative of locally finite variation, with no hypothesis on the
    original f outside [a,b]. This uses the localisation already used in
    2.5.18(2), p. 112. The local Federer erratum has no entry for this
    formula. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CurveVariationUP CurveArcLength
  StieltjesIntegral StieltjesSubstitution.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_interval_retracted_curve_variation]: supporting
    localisation of the printed hypothesis V_a^b f<infinity in
    Federer 2.9.24, p. 169. The retracted curve has finite
    variation on every interval, including intervals outside [a,b]. *)
Lemma finite_interval_retracted_curve_variation (R : realType) (f : R -> R)
    (a b : R) : a<=b ->
  (curve_variation (f : R -> real_line_metric R) a b < +oo)%E ->
  curve_locally_finite_variation (f \o @segment_retraction R a b : R -> real_line_metric R).
Proof.
move=> hab hV u v huv.
have hmono := @segment_retraction_monotone R a b.
apply: le_lt_trans (@curve_variation_comp_le R f (@segment_retraction R a b) u v hmono huv) _.
apply: le_lt_trans _ hV; apply: curve_variation_monotone.
- by have /andP[] := segment_retraction_bounds u hab.
- exact: hmono.
- by have /andP[_] := segment_retraction_bounds v hab.
Qed.

(** Source for [finite_interval_curve_value_bound]: supporting bounded image
    of the BV function f used in the bounded-convergence step of Federer
    2.9.24, p. 169. The real bound here is |f(a)|+V_a^b f. *)
Lemma finite_interval_curve_value_bound (R : realType) (f : R -> R)
    (a b : R) : a<=b ->
  (curve_variation (f : R -> real_line_metric R) a b < +oo)%E ->
  exists M : R, 0<=M /\ forall x : R, a<=x -> x<=b -> `|f x|<=M.
Proof.
move=> hab hV.
have hnon := @curve_variation_nonnegative R [the metricType R of real_line_metric R] f a b hab.
have hfin : curve_variation (f : R -> real_line_metric R) a b \is a fin_num.
  rewrite fin_numElt hV andbT; exact: lt_le_trans (ltNyr 0) hnon.
pose V := fine (curve_variation (f : R -> real_line_metric R) a b).
have hVexact : V%:E=curve_variation (f : R -> real_line_metric R) a b by rewrite /V fineK.
have hV0 : 0<=V by move: hnon; rewrite -hVexact lee_fin.
exists (`|f a|+V); split; first exact: addr_ge0 (normr_ge0 _) hV0.
move=> x hax hxb.
have hd := @curve_variation_ge_distance R [the metricType R of real_line_metric R] f a x hax.
have hm := @curve_variation_monotone R [the metricType R of real_line_metric R]
  f a a x b (lexx _) hax hxb.
have hb := le_trans hd hm; rewrite -hVexact lee_fin real_line_metric_distanceE distrC in hb.
have he : f x=f a+(f x-f a) by rewrite addrC subrK.
rewrite he; exact: le_trans (ler_normD _ _) (lerD (lexx _) hb).
Qed.
