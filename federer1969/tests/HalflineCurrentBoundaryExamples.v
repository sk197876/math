(** Federer (1969), 4.1.7, p. 359:
    actual unit-interval half-line regressions.
    Finite normal mass does not supply
    compact support or support-properness. Two distinct
    original whole-line primitives refute bare
    uniqueness, while the displayed primitive has
    the correct pushed boundary and fails
    the required support inclusion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentNormalMass NormalCurrentsUP CurrentProperSupport
  HalflineCurrents HalflineFiniteNormalMass HalflineCurrentTopology HalflineCurrentExample
  HalflinePrimitiveNonuniqueness HalflineSecondPrimitive HalflinePrimitiveBoundary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section HalflineCurrentBoundaryExamples.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 1)).
Local Notation U := (@current_halfline_domain R).
Local Notation hU := (@current_halfline_domain_open R).
Local Notation T := (@halfline_current R h2 1).
Local Notation Full := (fun _:X=>True).
Local Notation hImage := (fun (x:X) (_:U x)=>Logic.I).

(** Source for [unit_halfline_finite_mass_not_normal]:
    at b = 1 the actual original T
    has finite N but is not
    normal, a regression for Federer
    4.1.7, p. 359. The normality
    definition retains compactness of support in U. *)
Example unit_halfline_finite_mass_not_normal:
  (@current_normal_mass R h2 1 U hU 1%N T < +oo)%E /\
  ~@is_normal_current R h2 1 U hU 1%N T.
Proof.
split;first exact:(@halfline_current_normal_mass_bound R h2 1 ltr01).1.
exact:(@halfline_current_not_normal R h2 1 ltr01).
Qed.

(** Source for [unit_halfline_inclusion_not_proper]:
    the actual b = 1 inclusion fails
    properness on spt T, a
    regression for Federer 4.1.7, p. 359.
    Its original smoothness and Lipschitz bound
    do not remove this hypothesis. *)
Example unit_halfline_inclusion_not_proper:
  ~@is_current_proper_on_support R h2 1 1 1%N U hU Full T id hImage.
Proof. exact:(@halfline_inclusion_not_proper R h2 1 ltr01). Qed.

(** Source for [unit_halfline_two_distinct_primitives]:
    the two actual original integral currents
    at b = 1 are distinct despite
    equal point-mass boundaries, a counterexample
    regression for the unqualified uniqueness phrase
    in Federer 4.1.7, p. 359. *)
Example unit_halfline_two_distinct_primitives:
  @halfline_left_primitive_candidate R h2 1<>
    @halfline_right_primitive_candidate R h2 1.
Proof. exact:(@halfline_primitive_nonuniqueness R h2 1).2.2. Qed.
End HalflineCurrentBoundaryExamples.
