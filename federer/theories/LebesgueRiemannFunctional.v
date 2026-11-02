(** Supporting Riemann-to-Lebesgue identification for Federer (1969),
    2.6.3(2), pp. 117–118, from the characterisation of L^1 in 2.5.17, p.
    111. Only the abstract characterisation of the sealed scalar measure is
    used; its private witness is not imported. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground LebesgueLineUP LebesgueScalarMeasure
  LebesgueLineCharacterisation RealIntegralFunctionalUP CompactSupportFunctionUP StieltjesDaniellIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lebesgue_scalar_riemann_functional]: supporting
    identification of the sealed L^1 integral with the
    Riemann functional on K(R), Federer 2.5.17,
    p. 111, used for the evaluations in 2.6.3(2),
    pp. 117–118. Uniqueness of the Borel-regular
    interval-length measure transfers the existing theorem. *)
Theorem lebesgue_scalar_riemann_functional (R : realType) :
  is_real_integral_functional (@lebesgue_scalar_measure R)
    (@compactly_supported_continuous_functions R R)
    (induced_daniell (fun x : R => x)).
Proof.
have [mu [hm [hb [_ [_ [hi [hs _]]]]]]] := @lebesgue_line_measure_characterisation R.
have hmu : is_lebesgue_line_measure mu by constructor.
have he := lebesgue_line_unique (lebesgue_scalar_specification R) hmu.
by rewrite he.
Qed.
