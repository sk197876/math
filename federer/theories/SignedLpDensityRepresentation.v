(** Federer (1969), 2.5.7, p. 99: represent both variations and take
    k=k+-k-, then extend from L+ to L. The hypotheses below are the Daniell
    laws and the proved norm bound; the final theorem obtains them from the
    book's bounded-linearity assumptions. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP CountablyMeasurableUP FunctionLatticeUP VectorFunctionLattice
  DaniellIntegralUP DaniellIntegralNegation DaniellVariationUP DaniellVariation DaniellVariationBounds
  DaniellVariationFunctionals TotalScalarLpUP TotalScalarLpLattice TotalScalarLpFiniteSeminorm
  TotalScalarPairingValue TotalLpPairingLinear LpConjugatePair LpVariationBound
  MaximalDensityRepresentation PositivePartFunctionalDetermination.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [bounded_lp_daniell_density]: signed representing density in
    Federer 2.5.7, p. 99 The density belongs to the full conjugate Lq space,
    including countably measurable support. *)
Theorem bounded_lp_daniell_density (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q (A : (X -> R) -> R) (M : R) :
  is_lp_conjugate_pair p q -> (q=+oo -> measure_countably_measurable mu setT) -> (0 <= M)%R ->
  is_daniell_integral (total_scalar_lp mu p) A ->
  (forall f, total_scalar_lp mu p f -> (`|A f| <= M*finite_total_scalar_lp_norm mu p f)%R) ->
  exists k : X -> R, total_scalar_lp mu q k /\
    forall f, total_scalar_lp mu p f -> A f=total_scalar_pairing mu f k.
Proof.
move=> hpq hX hM hA hb.
pose L := total_scalar_lp mu p.
have hVL := @total_scalar_lp_vector_lattice R X mu hm p (lp_conjugate_pair_admissible hpq).1.
have hL := hVL.1.
pose P := @daniell_positive_variation R X L A hL hA.
pose Q := @daniell_negative_variation R X L A hL hA.
have hP := @daniell_positive_variation_specification R X L A hL hA.
have hQ := @daniell_negative_variation_specification R X L A hL hA.
have hPm := @positive_variation_monotone_daniell R X L A P hL hA hP.
have hQm := @negative_variation_monotone_daniell R X L A Q hL hA hQ.
have hP0 f := @daniell_positive_variation_nonnegative R X L A P hL hA hP f.
have hAn := @daniell_integral_negate R X L A hL hA.
have hQ0 f := @daniell_positive_variation_nonnegative R X L (fun f => (-A f)%R) Q hL hAn hQ f.
have hPb := @lp_positive_variation_norm_bound R X mu hm p A P M hM hb hP.
have hbn f : L f -> (`|-A f| <= M*finite_total_scalar_lp_norm mu p f)%R.
  by move=> hf; rewrite normrN; exact: hb f hf.
have hQb := @lp_positive_variation_norm_bound R X mu hm p (fun f => (-A f)%R) Q M hM hbn hQ.
have [kplus [hkp [hkp0 hPrepr]]] := @positive_lp_functional_density R X mu hm p q P M hpq hX hM hPm hP0 hPb.
have [kminus [hkm [hkm0 hQrepr]]] := @positive_lp_functional_density R X mu hm p q Q M hpq hX hM hQm hQ0 hQb.
pose k x := (kplus x-kminus x)%R.
have hk := @total_scalar_lp_subtract R X mu hm q kplus kminus hkp hkm.
exists k; split; first exact: hk.
apply: (@vector_lattice_additive_positive_determination R X L A (fun f => total_scalar_pairing mu f k)
  hVL (@daniell_integral_add R X L A hA)
  (@total_lp_pairing_linear R X mu hm p q k hpq hk).1)=> f hf.
rewrite (@daniell_positive_negative_identity R X L A P Q hL hA hP hQ f hf)
  (hPrepr f hf) (hQrepr f hf).
exact: esym (@total_lp_pairing_subtract_density R X mu hm p q f kplus kminus hpq hf.1 hkp hkm).
Qed.
