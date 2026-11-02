(** Federer (1969), 2.5.1, p. 92, final paragraph: the integral map on a
    summable sublattice preserves addition, positive homogeneity, order and
    increasing convergence. The functional is exposed only through the
    sealed integral laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUniqueness MeasureIntegralComparison FunctionLatticeUP MonotoneDaniellIntegralUP
  SummableRealFunctionUP SummableRealArithmetic RealIntegralIncreasingContinuity
  RealIntegralFunctionalUP RealIntegralFunctionalSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_integral_functional_is_monotone_daniell]: all four
    preservation properties in Federer 2.5.1, p. 92 Only the abstract
    integral specification of A is needed for this forward implication. *)
Theorem real_integral_functional_is_monotone_daniell (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (L : set (X -> R)) (A : (X -> R) -> R) :
  is_function_lattice L -> is_real_integral_functional mu L A -> is_monotone_daniell_integral L A.
Proof.
move=> hL hA; constructor.
- move=> f g hf hg.
  have hi := hA _ (function_lattice_add hL hf hg).
  have hi' := @real_total_integral_add R X mu hm f g (A f) (A g) (hA f hf) (hA g hg).
  have he := measure_integral_unique hi hi'; by injection he.
- move=> c f hc hf.
  have hi := hA _ (function_lattice_scale hL hc hf).
  have hi' := @real_total_integral_scale R X mu hm f (A f) c (hA f hf).
  have he := measure_integral_unique hi hi'; by injection he.
- move=> f g hf hg hfg.
  have hle : measure_almost_everywhere mu (partial_extended_le_locus (real_total_integrand f) (real_total_integrand g)).
    apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
    exists (f x)%:E,(g x)%:E; split; first by apply/real_total_integrand_graph.
    split; first by apply/real_total_integrand_graph.
    by rewrite lee_fin; exact: hfg.
  have hh := @measure_integral_monotone R X mu hm _ _ (A f)%:E (A g)%:E (hA f hf) (hA g hg) hle.
  by move: hh; rewrite lee_fin.
- move=> f g hf hg hinc.
  exact: (@real_integral_increasing_continuity R X mu hm f g (fun n => A (f n)) (A g)
    (fun n => hA (f n) (hf n)) (hA g hg) hinc).
Qed.

(** Source for [lattice_measure_integral]: the real integral map on L in
    Federer 2.5.1, p. 92 Off-L values of this ambient representative are
    unspecified and never used by the laws. *)
Definition lattice_measure_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (L : set (X -> R)) (hL : L `<=` summable_real_functions mu) :=
  @RealIntegralFunctional.value R X mu L hL.

(** Source for [lattice_measure_integral_specification]: integral
    characterisation of the map in Federer 2.5.1, p. 92 *)
Lemma lattice_measure_integral_specification (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (L : set (X -> R)) (hL : L `<=` summable_real_functions mu) :
  is_real_integral_functional mu L (@lattice_measure_integral R X mu L hL).
Proof. exact: RealIntegralFunctional.laws. Qed.

(** Source for [summable_sublattice_integral_laws]: complete final paragraph
    of Federer 2.5.1, p. 92 Existence and all four laws hold also for the
    empty sublattice. *)
Theorem summable_sublattice_integral_laws (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (L : set (X -> R))
    (hL : L `<=` summable_real_functions mu) : is_function_lattice L ->
  is_monotone_daniell_integral L (@lattice_measure_integral R X mu L hL).
Proof.
move=> hl; exact: (@real_integral_functional_is_monotone_daniell R X mu hm L _ hl
  (@lattice_measure_integral_specification R X mu L hL)).
Qed.
