(** Federer (1969), 2.5.9, p. 100: the dominated Daniell functional is
    L1-Lipschitz on its original lattice. The present difference estimate is
    supporting infrastructure. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureIntegralUniqueness FunctionLatticeUP
  MonotoneDaniellIntegralUP DaniellIntegralUP RealIntegralFunctionalUP
  TotalScalarLpUP TotalScalarLpLattice TotalScalarLpFiniteSeminorm TotalScalarPairing
  RegularLatticeLoneDensity ScalarLipschitzExtensionUP FunctionSeminormDistance LatticeDominatedDifference.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dominated_lattice_lone_lipschitz]: quantitative
    continuity for Federer 2.5.9, p. 100, retaining
    the original lattice, without assuming closure under negation. *)
Lemma dominated_lattice_lone_lipschitz (R : realType) (X : choiceType)
    (L : set (X -> R)) (hL : is_function_lattice L) (F A : (X -> R) -> R)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  is_monotone_daniell_integral L F -> is_real_integral_functional mu L F ->
  is_daniell_integral L A ->
  (forall f, L f -> (`|A f| <= F (fun x => `|f x|))%R) ->
  is_scalar_lipschitz_on_set L (function_seminorm_distance (finite_total_scalar_lp_norm mu 1)) A.
Proof.
move=> hF hrepr hA hb f g hf hg.
have hfm := @represented_lattice_in_total_lone R X mu hm L F hrepr f hf.
have hgm := @represented_lattice_in_total_lone R X mu hm L F hrepr g hg.
have hd := @total_scalar_lp_subtract R X mu hm 1 f g hfm hgm.
have habs := @lattice_absolute_difference_member R X L hL f g hf hg.
have hi := hrepr _ habs.
have hNi := @total_scalar_lone_absolute_integral R X mu hm _ hd.
have he : finite_total_scalar_lp_norm mu 1 (fun x => (f x-g x)%R)=F (fun x => `|f x-g x|%R).
  exact: EFin_inj (measure_integral_unique hNi hi).
rewrite /function_seminorm_distance he.
exact: (@lattice_dominated_difference_bound R X L hL A F hA hF hb f g hf hg).
Qed.
