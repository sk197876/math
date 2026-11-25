(** Federer (1969), 2.5.10, p. 100, and 2.5.11, p. 102: the negative answer
    to the question of 2.5.10 without hypotheses. The sets Y_1 and Y_2 with
    cardinal numbers aleph_1 and aleph_2, presupposed in 2.5.11, exist
    (CardinalSuccessorExistence.v), and the example of 2.5.11 then gives a
    monotone Daniell integral lambda with L regular measure phi, L_1(phi)=L,
    and a functional mu on all phi summable functions with M <= 1 which is
    represented by no phi measurable function k, whether k is real valued or
    extended real valued with either reading of 0 . infinity in 2.1.1, p.
    51. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import CardinalSuccessorUP CardinalSuccessorExistence
  CardinalProductExample CardinalProductCounterexample CardinalProductLoneIdentity
  CardinalProductLoneFunctional MeasureUP FunctionLatticeUP FunctionLatticeRegularityUP
  MonotoneDaniellIntegralUP DaniellIntegralUP RealIntegralFunctionalUP
  FunctionLatticeSeminormUP FunctionOperatorSeminorm TotalScalarLpUP TotalScalarLpFiniteSeminorm
  RealLatticeDensityUP ExtendedLatticeDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section ExtendedNoDensity.
Variable R : realType.
Variables J1 J2 : choiceType.
Hypothesis h1 : is_cardinal_successor (@setT nat) (@setT J1).
Hypothesis h2 : is_cardinal_successor (@setT J1) (@setT J2).
Variable phi : set (J1 * J2) -> \bar R.
Hypothesis hm : is_measure phi.
Hypothesis hA : is_real_integral_functional phi (@example_lattice R J1 J2 h1) (@example_lambda R J1 J2 h1).
Hypothesis hr : is_function_lattice_regular (@example_lattice R J1 J2 h1) phi.

Local Notation mu := (@example_mu R J1 J2 h1).

(** Source for [example_no_extended_density]: Federer 2.5.10,
    p. 100, and 2.5.11, p. 102: no phi measurable extended real k
    satisfies mu(f)=integral f k d phi whenever f is phi summable,
    with the partial product of 2.1.1, p. 51. *)
Theorem example_no_extended_density (k : J1 * J2 -> \bar R) :
  ~ is_extended_lattice_density phi (total_scalar_lp phi 1) mu k.
Proof.
move=> hk; exact: (@example_lone_no_density R J1 J2 h1 h2 phi hm hA hr _
  (extended_lattice_density_real hm hk)).
Qed.

(** Source for [example_no_zero_product_density]: the same
    conclusion of Federer 2.5.10, p. 100, and 2.5.11, p. 102, with
    the convention 0 . infinity = 0 of 2.1.1, p. 51. *)
Theorem example_no_zero_product_density (k : J1 * J2 -> \bar R) :
  ~ is_zero_product_lattice_density phi (total_scalar_lp phi 1) mu k.
Proof.
move=> hk; exact: (@example_lone_no_density R J1 J2 h1 h2 phi hm hA hr _
  (zero_product_lattice_density_real hm hk)).
Qed.

End ExtendedNoDensity.

(** Source for [federer_2_5_10_negative_answer_unconditional]: the
    sentence "Example 2.5.11 shows that in general the answer is no"
    in Federer 2.5.10, p. 100, without hypotheses: the sets Y_1, Y_2
    of 2.5.11, p. 102, exist, phi is the L regular measure of the
    monotone Daniell integral lambda, L_1(phi)=L, |mu(f)| <=
    lambda(|f|) on L, mu is linear on all phi summable functions with
    M <= 1, and no phi measurable real or extended real k represents
    mu on all phi summable functions. *)
Theorem federer_2_5_10_negative_answer_unconditional (R : realType) :
  exists (J1 J2 : choiceType),
    is_cardinal_successor (@setT nat) (@setT J1) /\ is_cardinal_successor (@setT J1) (@setT J2) /\
  exists (L : set (J1 * J2 -> R)) (lambda mu : (J1 * J2 -> R) -> R) (phi : set (J1 * J2) -> \bar R),
    is_function_lattice L /\ is_monotone_daniell_integral L lambda /\
    is_measure phi /\ is_real_integral_functional phi L lambda /\ is_function_lattice_regular L phi /\
    is_daniell_integral L mu /\
    (forall f, L f -> (`|mu f| <= lambda (fun x => `|f x|))%R) /\
    total_scalar_lp phi 1 = L /\
    is_linear_functional_on_functions (total_scalar_lp phi 1) mu /\
    function_operator_seminorm (total_scalar_lp phi 1) mu (finite_total_scalar_lp_norm phi 1) <= 1 /\
    (forall k : J1 * J2 -> R, ~ is_real_lattice_density phi (total_scalar_lp phi 1) mu k) /\
    (forall k : J1 * J2 -> \bar R, ~ is_extended_lattice_density phi (total_scalar_lp phi 1) mu k) /\
    (forall k : J1 * J2 -> \bar R, ~ is_zero_product_lattice_density phi (total_scalar_lp phi 1) mu k).
Proof.
have [J1 [J2 [h1 h2]]] := aleph_one_two_exist.
exists J1, J2; split=> //; split=> //.
have [phi [hm [hA hr]]] := @example_regular_measure_exists R J1 J2 h1.
exists (@example_lattice R J1 J2 h1), (@example_lambda R J1 J2 h1), (@example_mu R J1 J2 h1), phi.
split; first exact: example_lattice_is_lattice.
split; first exact: example_lambda_monotone_daniell.
split=> //; split=> //; split=> //.
split; first exact: example_mu_daniell.
split; first by move=> f hf; exact: (example_mu_absolute_bound hf).
split; first exact: (example_lone_identity hm hA hr).
split; first exact: (example_mu_lone_linear hm hA hr).
split; first exact: (example_mu_operator_seminorm hm hA hr).
split; first by move=> k; exact: (example_lone_no_density h2 hm hA hr (k := k)).
split; first by move=> k; exact: (example_no_extended_density h2 hm hA hr (k := k)).
by move=> k; exact: (example_no_zero_product_density h2 hm hA hr (k := k)).
Qed.
