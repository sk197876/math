(** Federer (1969), 2.5.8, p. 100: the two variations bound the functional
    on an order interval. Here domination may hold almost everywhere:
    clipping to the interval changes a test only on a null set, and the
    corrected null-norm hypothesis preserves its value (erratum p. 2, book
    p. 100 line 3). *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureAlmostUP MeasureAlmostBasic FunctionLatticeUP FunctionLatticeLaws
  VectorFunctionLattice FunctionLatticeSeminormUP DaniellIntegralUP DaniellVariationUP DaniellVariation
  DaniellVariationFunctionals VectorVariationFiniteBounds TotalScalarLpUP TotalScalarLpLattice
  DaniellVectorLinearity LpNullRespectingFunctional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [lp_daniell_almost_order_bound]: supporting finite variation
    bound in Federer 2.5.8, p. 100 The bound is uniform over the entire
    almost order interval, and does not presuppose a bounded operator norm. *)
Lemma lp_daniell_almost_order_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p (A : (X -> R) -> R) :
  1 <= p -> is_daniell_integral (total_scalar_lp mu p) A ->
  (forall f, total_scalar_lp mu p f -> total_scalar_lp_norm mu p f=0 -> A f=0%R) ->
  forall g, total_scalar_lp mu p g -> (forall x, (0 <= g x)%R) ->
    exists b : R, forall f, total_scalar_lp mu p f ->
      measure_almost_everywhere mu [set x | (`|f x| <= g x)%R] -> (`|A f| <= b)%R.
Proof.
move=> hp hA hnull g hg hg0.
have hL := @total_scalar_lp_vector_lattice R X mu hm p hp.
have hlin := @vector_daniell_integral_linear R X _ A hL hA.
pose P := @daniell_positive_variation R X _ A hL.1 hA.
pose Q := @daniell_negative_variation R X _ A hL.1 hA.
have hP := @daniell_positive_variation_specification R X _ A hL.1 hA.
have hQ := @daniell_negative_variation_specification R X _ A hL.1 hA.
exists (P g+Q g)%R=> f hf hae.
pose t x := Order.max (Order.min (f x) (g x)) (-g x)%R.
have ht : total_scalar_lp mu p t.
  apply: (@function_lattice_maximum R X _ hL.1).
  - exact: (@total_scalar_lp_minimum R X mu hm p f g hf hg).
  - exact: (@vector_function_lattice_negation R X _ hL g hg).
have hft : measure_almost_everywhere mu [set x | f x=t x].
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hae)=> x hx.
  have hh : (`|f x| <= g x)%R := hx.
  rewrite ler_norml in hh; have [hlo hhi] := andP hh.
  change (f x=t x); by rewrite /t min_l // max_l.
have he := @lp_null_respecting_functional_almost_equal R X mu hm p A hp hlin hnull f t hf ht hft.
rewrite he; apply: (@finite_variation_sum_upper R X _ A hL hlin.1 g (P g) (Q g)).
- by split.
- exact: hP g (conj hg hg0).
- exact: hQ g (conj hg hg0).
- split=> // x; rewrite /t ler_norml; apply/andP; split.
  + by rewrite le_max lexx orbT.
  + rewrite ge_max; apply/andP; split.
    * by rewrite ge_min lexx orbT.
    * have hn : (-g x <= 0)%R by rewrite oppr_le0; exact: hg0.
      exact: le_trans hn (hg0 x).
Qed.
