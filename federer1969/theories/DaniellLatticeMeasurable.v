(** Federer (1969), proof of 2.5.2, p. 93: every positive lattice member is
    measurable for the envelope measure, by the criterion 2.3.2(7), pp.
    74–75. The adapter below retains the exact total domain when applying
    the earlier partial-function criterion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws MonotoneDaniellIntegralUP
  DaniellCoverUP DaniellCoverMeasure DaniellLevelSeparation SummableRealFunctionUP
  PartialFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasurableSeparationUP MeasurableLevelCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_total_lower_level]: supporting graph identification of
    {f <= a} for the invocation of 2.3.2(7) in Federer 2.5.2, p. 93 The real
    function is embedded into the extended line. *)
Lemma real_total_lower_level (R : realType) (X : Type) (f : X -> R) a :
  partial_function_preimage (real_total_integrand f) [set y | y <= a%:E]=
    [set x | (f x <= a)%R].
Proof.
apply/seteqP; split.
- move=> x [y [hy hya]]; have he := (real_total_integrand_graph f x y).1 hy.
  change (is_true (y <= a%:E)) in hya.
  change (is_true ((f x <= a)%R)).
  by move: hya; rewrite -he lee_fin.
- move=> x hx; exists (f x)%:E; split; first by apply/real_total_integrand_graph.
  change (is_true ((f x)%:E <= a%:E)); by rewrite lee_fin.
Qed.

(** Source for [real_total_upper_level]: supporting graph identification of
    {f >= b} in Federer 2.5.2, p. 93 *)
Lemma real_total_upper_level (R : realType) (X : Type) (f : X -> R) b :
  partial_function_preimage (real_total_integrand f) [set y | b%:E <= y]=
    [set x | (b <= f x)%R].
Proof.
apply/seteqP; split.
- move=> x [y [hy hby]]; have he := (real_total_integrand_graph f x y).1 hy.
  change (is_true (b%:E <= y)) in hby.
  change (is_true ((b <= f x)%R)).
  by move: hby; rewrite -he lee_fin.
- move=> x hx; exists (f x)%:E; split; first by apply/real_total_integrand_graph.
  change (is_true (b%:E <= (f x)%:E)); by rewrite lee_fin.
Qed.

(** Source for [daniell_positive_lattice_measurable]: the conclusion that
    every f in L+ is phi measurable in Federer 2.5.2, p. 93 This proves
    measurability before identifying the integral value. *)
Theorem daniell_positive_lattice_measurable (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) (mu : set X -> \bar R)
    (hm : is_daniell_cover_envelope L A mu) (f : X -> R) :
  positive_function_lattice L f -> is_measure_measurable_function mu (real_total_integrand f).
Proof.
move=> hf; have hmeasure := daniell_cover_is_measure hL hA hm (function_lattice_zero hL hf.1).
have hd : measure_almost_everywhere mu (partial_function_domain (real_total_integrand f)).
  apply: (@measure_almost_everywhere_mono R X mu hmeasure setT _ _ (measure_almost_everywhere_true hmeasure))=> x _.
  exists (f x)%:E; by apply/real_total_integrand_graph.
apply/(measurable_extended_level_separation_iff hmeasure hd)=> T a b hab.
rewrite real_total_lower_level real_total_upper_level.
exact: (@daniell_positive_level_separation R X L A hL hA mu hm f hf T a b hab).
Qed.
