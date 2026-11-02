(** Federer (1969), 2.5.13, pp. 106–107: Riesz's representation theorem for
    an order-bounded linear functional on continuous compactly supported
    real functions. We apply the project's already proved 2.5.5. No external
    Riesz or measure-representation theorem is imported. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import FunctionLatticeUP DaniellIntegralUP FunctionLatticeSeminormUP
  MeasureUP MeasureIntegralUP SummableRealFunctionUP FunctionLatticeRegularityUP DaniellRepresentation
  CompactSupportFunctionUP CompactSupportFunctionLattice CompactSupportDaniellContinuity PositiveLatticeRegularity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_support_order_bounded_daniell]: first conclusion of
    Federer 2.5.13, p. 106, with the continuity proof on pp. 106–107 The
    upper bound is required only on the positive intervals in the printed
    hypothesis; other intervals are empty. *)
Theorem compact_support_order_bounded_daniell (R : realType) (X : topologicalType)
    (A : (X -> R) -> R) :
  hausdorff_space X -> locally_compact (@setT X) ->
  is_linear_functional_on_functions (@compactly_supported_continuous_functions R X) A ->
  (forall u, positive_function_lattice (@compactly_supported_continuous_functions R X) u ->
    exists b, forall k, lattice_positive_order_interval (@compactly_supported_continuous_functions R X) u k -> A k<=b) ->
  is_daniell_integral (@compactly_supported_continuous_functions R X) A.
Proof.
move=> hh hl hA hb; constructor.
- exact hA.1.
- move=> c f hc hf; exact: hA.2 c f hf.
- move=> f hf; case: (pselect (function_nonnegative f))=> hp.
  + exact: hb f (conj hf hp).
  + exists 0=> k [hk [hk0 hkf]]; exfalso; apply: hp=> x; exact: le_trans (hk0 x) (hkf x).
- exact (@compact_support_increasing_functional_limit R X A hh hl hA hb).
Qed.

(** Source for [compact_support_riesz_representation]: complete
    measure-representation conclusion of Federer 2.5.13, p. 106 The two
    measures are L regular, and every lattice function has an actual finite
    integral against each, with their difference equal to the functional.
    Radon regularity is not asserted here; Federer treats that distinction
    in 2.5.14–2.5.15. *)
Theorem compact_support_riesz_representation (R : realType) (X : topologicalType)
    (A : (X -> R) -> R) :
  hausdorff_space X -> locally_compact (@setT X) ->
  is_linear_functional_on_functions (@compactly_supported_continuous_functions R X) A ->
  (forall u, positive_function_lattice (@compactly_supported_continuous_functions R X) u ->
    exists b, forall k, lattice_positive_order_interval (@compactly_supported_continuous_functions R X) u k -> A k<=b) ->
  exists mu nu : set X -> \bar R,
    is_measure mu /\ is_measure nu /\
    is_function_lattice_regular (@compactly_supported_continuous_functions R X) mu /\
    is_function_lattice_regular (@compactly_supported_continuous_functions R X) nu /\
    forall f, compactly_supported_continuous_functions f -> exists a b : R,
      is_measure_integral mu (real_total_integrand f) a%:E /\
      is_measure_integral nu (real_total_integrand f) b%:E /\ A f=a-b.
Proof.
move=> hh hl hA hb.
have hD := @compact_support_order_bounded_daniell R X A hh hl hA hb.
have hne : exists f : X -> R, compactly_supported_continuous_functions f.
  exists (fun _ => 0); exact: compactly_supported_zero_function.
have [P [Q [mu [nu [hP [hQ [hm [hn [hr [hs [hi [hj [hformula hsep]]]]]]]]]]]]] :=
  @daniell_integral_representation R X (@compactly_supported_continuous_functions R X) A
    (@compactly_supported_continuous_functions_lattice R X) hD hne.
exists mu,nu; split=> //; split=> //; split.
- exact: (@function_lattice_regular_positive_iff R X _ mu).1 hr.
- split; last exact hformula.
  exact: (@function_lattice_regular_positive_iff R X _ nu).1 hs.
Qed.
