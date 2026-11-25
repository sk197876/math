(** The common finite Borel hulls in Federer (1969), 2.9.6, p. 155. Apply
    2.1.4 to simultaneous phi and psi_phi hulls, compare their intersection
    using 2.9.4 at distinct positive bounds, and discard the null overlap.
    We localise inside a bounded Borel parent; the original M gives every
    required finite mass. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureHull BorelRegularMeasureUP
  TopologicalBorel CoveringFamilyUP MeasureDerivationContext MeasureDerivates PartialFunctionUP
  AbsoluteContinuousPart ContinuousPartDecomposition ContinuousPartDecompositionUP
  CommonBorelHulls DerivationComparison DerivationExceptionalArithmetic NullHullSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [derivation_bounded_strict_separation]: the
    bounded-set argument of Federer 2.9.6, p. 155.
    Targets in strict derivative levels separated by
    0<a<b have additive lower measure bound. The
    bounded Borel parent supplies only proof localisation;
    no measurability of either target is assumed. *)
Lemma derivation_bounded_strict_separation (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop)
    (K A B : set X) (a b : R) :
  is_measure_derivation_context phi V -> is_derivation_measure psi ->
  borel_set K -> metric_set_bounded K -> A `<=` K -> B `<=` K -> (0<a)%R -> (a<b)%R ->
  (forall x, A x -> exists y, partial_function_graph (measure_derivate psi phi V) x y /\ y<a%:E) ->
  (forall x, B x -> exists y, partial_function_graph (measure_derivate psi phi V) x y /\ b%:E<y) ->
  phi A+phi B<=phi (A `|` B).
Proof.
move=> hc hp hK hKb hAK hBK ha hab hAlow hBup.
have hf := derivation_context_measure hc.
have hm := derivation_measure_law hf.
have hr := derivation_measure_borel_regular hf.
pose gamma := measure_continuous_part psi phi.
have [E [hdecomp _]] := @measure_continuous_part_decomposition R X phi psi hf hp.
have hg := continuous_decomposition_class hdecomp.
have hmg := derivation_measure_law hg.
have hrg := derivation_measure_borel_regular hg.
have hphiK := @derivation_measure_bounded_finite R X phi hf K hKb.
have hgammaK := @derivation_measure_bounded_finite R X gamma hg K hKb.
have hphiA := le_lt_trans (@measure_mono R X phi hm A K hAK) hphiK.
have hphiB := le_lt_trans (@measure_mono R X phi hm B K hBK) hphiK.
have hgammaA := le_lt_trans (@measure_mono R X gamma hmg A K hAK) hgammaK.
have hgammaB := le_lt_trans (@measure_mono R X gamma hmg B K hBK) hgammaK.
have [U [hU [hAU [hUK [hphia hga]]]]] := @common_borel_hull_inside R X phi gamma K A hm hmg hr hrg hK hAK.
have [W [hW [hBW [hWK [hphib hgb]]]]] := @common_borel_hull_inside R X phi gamma K B hm hmg hr hrg hK hBK.
have hUm := @borel_regular_borel_measurable R X phi hm hr U hU.
have hWm := @borel_regular_borel_measurable R X phi hm hr W hW.
have hUgm := @borel_regular_borel_measurable R X gamma hmg hrg U hU.
have hWgm := @borel_regular_borel_measurable R X gamma hmg hrg W hW.
have hphiAh := @measure_hull_of_finite_equal_measure R X phi hm A U hAU hUm hphia hphiA.
have hphiBh := @measure_hull_of_finite_equal_measure R X phi hm B W hBW hWm hphib hphiB.
have hgammaAh := @measure_hull_of_finite_equal_measure R X gamma hmg A U hAU hUgm hga hgammaA.
have hgammaBh := @measure_hull_of_finite_equal_measure R X gamma hmg B W hBW hWgm hgb hgammaB.
have ephiA : phi (A `&` W)=phi (U `&` W).
  have h := @measure_hull_test R X phi A U hphiAh W hWm.
  by rewrite (setIC W A) (setIC W U) in h.
have egammaA : gamma (A `&` W)=gamma (U `&` W).
  have h := @measure_hull_test R X gamma A U hgammaAh W hWgm.
  by rewrite (setIC W A) (setIC W U) in h.
have ephiB := @measure_hull_test R X phi B W hphiBh U hUm.
have egammaB := @measure_hull_test R X gamma B W hgammaBh U hUgm.
have hlow : gamma (U `&` W)<=a%:E*phi (U `&` W).
  rewrite -egammaA -ephiA.
  apply: (@derivation_lower_comparison R X phi psi V (A `&` W) a hc hp ha)=> x [hx _].
  have [y [[_ [_ hl]] hya]] := hAlow x hx; by rewrite hl.
have hb : (0<b)%R := lt_trans ha hab.
have hup : b%:E*phi (U `&` W)<=gamma (U `&` W).
  rewrite -egammaB -ephiB.
  apply: (@derivation_upper_comparison R X phi psi V (U `&` B) b hc hp hb)=> x [_ hx].
  have [y [[_ [hu _]] hby]] := hBup x hx; by rewrite hu.
have hfinite : phi (U `&` W)< +oo.
  apply: le_lt_trans _ hphiK; apply: (@measure_mono R X phi hm)=> x [hx _]; exact: hUK x hx.
have hz := @finite_separated_scaled_bounds_zero R (phi (U `&` W)) (gamma (U `&` W))
  a b (measure_nonnegative hm _) hfinite hab hup hlow.
exact (@null_overlap_measurable_covers_separate R X phi A B U W hm hAU hBW hUm hz).
Qed.
