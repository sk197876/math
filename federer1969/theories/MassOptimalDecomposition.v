(** Federer (1969), 1.8.1, p. 38, final display: mass is the sum of
    Euclidean lengths in a simple decomposition having at most binomial(dim
    V,m) terms. The empty decomposition handles zero, including
    zero-dimensional powers. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP ExteriorGrading ExteriorNorm
  AlternatingCoordinates LinearBasis FiniteExteriorPowers FiniteOrdinalBasis
  ExteriorIndices AssociatedSubspace SimpleElementary SimpleUnitBall
  ComassUP MassUP MassBounds MassEquality MassHomogeneity MassSealed
  MassConvexHull MassDecompositionBound SubconvexCombinations SubconvexReduction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Decomposition.
Variable R : realType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Variable m : nat.
Hypothesis hm : (0 < m)%N.
Variable kappa : A_m V R^o m -> R.
Hypothesis hk : forall phi, is_comass h2 hB phi (kappa phi).
Local Notation E := (exterior_power V m).
Local Notation N := (@exterior_norm R h2 V B hB m).
Local Notation S := (@simple_unit_ball R h2 V B hB m).

(** Source for [mass_optimal_simple_decomposition]: Federer 1.8.1,
    p. 38, final display and preceding sentence, paraphrased above.
    This is an attained minimum, with the printed dimension bound;
    zero is represented by no terms. *)
Theorem mass_optimal_simple_decomposition x d : is_mass kappa x d ->
  exists k, exists u : 'I_k -> E,
    (k <= 'C(n,m))%N /\ (forall i, simple (u i)) /\
    x = \sum_i u i /\ d = \sum_i N (u i).
Proof.
move=> hd; have hd0 := @mass_nonnegative R h2 V B hB m hm kappa hk x d hd.
have [hz|hz] := eqVneq d 0.
- have hx : x = 0.
    apply: (@mass_definite R h2 V B hB n e he m hm kappa hk x).
    by rewrite -hz.
  exists 0%N, (fun _ => 0); split=> //; split.
  + move=> i; by have := ltn_ord i; rewrite ltn0.
  + by rewrite !big_ord0 hx hz.
have hdp : 0 < d by rewrite lt0r hz hd0.
pose y := d^-1 *: x.
pose dy := @Mass.norm R h2 V B hB n e he m hm kappa hk y.
have hdy := @Mass.laws R h2 V B hB n e he m hm kappa hk y.
have hdy1 : dy = 1.
  have hh := @mass_absolute_homogeneity R h2 V B hB m hm kappa hk x d^-1 d dy hd hdy.
  have hiv : 0 <= d^-1 by rewrite invr_ge0.
  by rewrite (ger0_norm hiv) mulVf // in hh.
have hy1 : is_mass kappa y 1 by rewrite -hdy1.
have hyC := (proj1 (@mass_unit_ball_iff_subconvex R h2 V B hB n e he m hm kappa hk y 1 hy1)) (lexx 1).
case: hyC => j [v [a [hv [ha [hs hy]]]]].
have hb := finite_ordinal_basis (@finite_e_lambda_basis R n V e he h2 m).
have [k [w [b [hkd [hw [hb0 [hbs hvw]]]]]]] :=
  @subconvex_dimension_reduction R E _ _ hb S j v a hv ha hs.
pose u i := (d*b i) *: w i.
have hu i : simple (u i) := simple_scale (d*b i) hm (proj1 (hw i)).
have hxu : x = \sum_i u i.
  have hxy : d *: y = x by rewrite /y scalerA mulfV // scale1r.
  rewrite -hxy hy hvw scaler_sumr; apply: eq_bigr => i _.
  by rewrite /u scalerA.
have hupper : \sum_i N (u i) <= d.
  have ht : \sum_i N (u i) <= d * \sum_i b i.
    rewrite mulr_sumr; apply: ler_sum => i _.
    rewrite /u exterior_norm_scale (ger0_norm (mulr_ge0 hd0 (hb0 i))).
    have hh := ler_wpM2l (mulr_ge0 hd0 (hb0 i)) (proj2 (hw i)).
    by rewrite mulr1 in hh.
  apply: (le_trans ht); have hh := ler_wpM2l hd0 hbs.
  by rewrite mulr1 in hh.
have hlower : d <= \sum_i N (u i).
  apply: (@simple_decomposition_mass_bound R h2 V B hB m hm kappa hk
    (Finite.clone 'I_k _) u d hu).
  by rewrite -hxu.
exists k, u; split; first by rewrite -card_Lambda.
split=> //; split=> //; apply/eqP; rewrite eq_le; exact/andP.
Qed.
End Decomposition.
