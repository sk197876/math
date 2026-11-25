(** Federer (1969), 2.5.2, pp. 92–93: representation of an additive,
    positively homogeneous, order-preserving and increasing-continuous
    lattice functional by a measure. This public interface uses only the
    sealed measure specification; the proof follows the suiting-sequence
    construction, level separation and layer limits. Empty lattices and
    lattices not closed under negation are included. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP MonotoneDaniellIntegralUP DaniellMeasureUP DaniellMeasureSealed
  DaniellCoverUP SummableRealFunctionUP RealIntegralFunctionalUP MeasureUP MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [monotone_daniell_measure]: the measure supplied by Federer
    2.5.2, p. 92 *)
Definition monotone_daniell_measure (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) := @DaniellMeasure.value R X L A hL hA.

(** Source for [monotone_daniell_measure_specification]: the measure and
    representation laws of Federer 2.5.2, pp. 92–93 *)
Lemma monotone_daniell_measure_specification (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) :
  is_monotone_daniell_measure L A (@monotone_daniell_measure R X L A hL hA).
Proof. exact: DaniellMeasure.laws. Qed.

(** Source for [monotone_daniell_measure_is_measure]: the measure conclusion
    of Federer 2.5.2, p. 92 *)
Lemma monotone_daniell_measure_is_measure (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) :
  is_measure (@monotone_daniell_measure R X L A hL hA).
Proof. exact: monotone_daniell_measure_laws (monotone_daniell_measure_specification hL hA). Qed.

(** Source for [monotone_daniell_measure_represents]: the equality
    lambda(f)=integral(f) for every f in L in Federer 2.5.2, p. 92 *)
Lemma monotone_daniell_measure_represents (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) :
  is_real_integral_functional (@monotone_daniell_measure R X L A hL hA) L A.
Proof. exact: monotone_daniell_measure_integral (monotone_daniell_measure_specification hL hA). Qed.

(** Source for [monotone_daniell_measure_summability]: the finite integral
    implicit in Federer 2.5.2, p. 92 *)
Lemma monotone_daniell_measure_summability (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) :
  L `<=` summable_real_functions (@monotone_daniell_measure R X L A hL hA).
Proof.
move=> f hf; exists (A f); exact: (@monotone_daniell_measure_represents R X L A hL hA f hf).
Qed.

(** Source for [monotone_daniell_measure_envelope]: the defining infimum in
    Federer 2.5.2, p. 92 Retaining this abstract law supports the uniqueness
    discussion and regularisation in the following item 2.5.3. *)
Lemma monotone_daniell_measure_envelope (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) : (exists f, L f) ->
  is_daniell_cover_envelope L A (@monotone_daniell_measure R X L A hL hA).
Proof. exact: monotone_daniell_measure_cover (monotone_daniell_measure_specification hL hA). Qed.

(** Source for [monotone_daniell_representation]: direct full existence
    theorem of Federer 2.5.2, p. 92 All hypotheses are the four printed
    functional laws on the printed function lattice. *)
Theorem monotone_daniell_representation (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) :
  is_function_lattice L -> is_monotone_daniell_integral L A ->
  exists mu, is_measure mu /\ is_real_integral_functional mu L A.
Proof.
move=> hL hA; exists (@monotone_daniell_measure R X L A hL hA); split.
- exact: monotone_daniell_measure_is_measure.
- exact: monotone_daniell_measure_represents.
Qed.
