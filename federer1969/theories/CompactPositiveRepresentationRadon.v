(** Federer (1969), 2.5.20, p. 114: the variation measure obtained from
    2.5.12 is Radon on compact metric X. Positive and negative parts extend
    its representation from K(X)+ to K(X), so the countable-base conclusion
    of 2.5.14, p. 107, applies to the same regular measure. Source context:
    CompactFunctionSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP RadonMeasureUP FunctionLatticeUP FunctionLatticeRegularityUP
  RealIntegralFunctionalUP PositiveDifferenceFunctional PositiveLatticeRegularity SummableRealArithmetic
  CompactSupportFunctionUP CompactSupportFunctionLattice CompactSupportCountableRadon
  CountableOpenBaseUP SubtypeCompactHausdorff VectorDaniellHypotheses LatticeSeriesCoverUP
  DaniellSpaceCompactSpace NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_parts_extend_integral_representation]:
    the parts identity of Federer 2.5.1, p. 91,
    extends the positive variation representation to K(X),
    supporting the Radon assertion in 2.5.20, p. 114. *)
Lemma positive_parts_extend_integral_representation (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (L : set (X -> R)) (hL : is_function_lattice L) (F : (X -> R) -> R) :
  is_real_integral_functional mu (positive_function_lattice L) F ->
  is_real_integral_functional mu L (positive_difference_functional F).
Proof.
move=> hF f hf; have [hp hn] := positive_parts_membership hL hf.
have hi := real_total_integral_subtract hm (hF _ hp) (hF _ hn).
by rewrite positive_parts_difference in hi.
Qed.

(** Source for [compact_positive_regular_representation_radon]:
    the measure yielded by 2.5.12 is Radon in the
    compact countable-base setting of Federer 2.5.20, p. 114,
    by 2.5.14, p. 107. No second measure is substituted. *)
Theorem compact_positive_regular_representation_radon (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (hm : is_measure mu) (F : (X -> R) -> R)
    (B : nat -> set X) :
  hausdorff_space X -> compact (@setT X) -> is_countable_open_base B ->
  is_real_integral_functional mu (positive_function_lattice (@compactly_supported_continuous_functions R X)) F ->
  is_function_lattice_regular (positive_function_lattice (@compactly_supported_continuous_functions R X)) mu ->
  is_radon_measure mu.
Proof.
move=> hh hc hB hF hr.
have hA := @positive_parts_extend_integral_representation R X mu hm
  (@compactly_supported_continuous_functions R X) (@compactly_supported_continuous_functions_lattice R X) F hF.
have hreg := (function_lattice_regular_positive_iff _ _).1 hr.
exact: (@compact_support_regular_countable_base_radon R X mu (positive_difference_functional F)
  hm hA hreg B hh (compact_space_locally_compact hc) hB).
Qed.

(** Source for [compact_function_lattice_unit_series]: the
    constant one supplies hypothesis (3) of 2.5.12,
    p. 103, for the compact domain in Federer 2.5.20,
    p. 114. This also covers an empty domain. *)
Lemma compact_function_lattice_unit_series (R : realType) (X : topologicalType) :
  compact (@setT X) -> has_lattice_unit_series (@compactly_supported_continuous_functions R X).
Proof.
move=> hX; exists (fun _ _ => (1 : R)); split.
- move=> n; split; first exact: @compact_space_constant_one R X hX.
  by move=> x; exact: ler01.
- move=> x _; have h := @nonnegative_sum_term R [the choiceType of (nat : Type)] setT
    (fun _ => (1 : R)%:E) 0%N I.
  exact h.
Qed.
