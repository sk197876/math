(** Federer (1969), 2.5.4(2), p. 96: "We observe that all Borel sets of R^2
    are phi_2 measurable". The L_2 regular measure phi_2 satisfies phi_2(S)
    = L^1[xi^{-1}(S) cap {t : 0 <= t <= 1}] with xi(t) = (t, 0); a set S is
    therefore phi_2 measurable whenever xi^{-1}(S) is L^1 measurable,
    because xi^{-1} commutes with intersections and differences. For a Borel
    set S the preimage under the continuous map xi is a Borel subset of R by
    2.2.11, and L^1 is Borel regular by 2.5.17, hence measures all Borel
    sets by 2.2.3. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground TopologicalBorel ContinuousBorelPreimages
  BorelRegularMeasureUP FunctionLatticeUP FunctionLatticeRegularityUP RealIntegralFunctionalUP
  MeasureUP CompactSupportFunctionUP StieltjesDaniellIntegral LebesgueLineMeasure
  PlaneRegularMeasureExamples StieltjesBorelRegularity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PlaneBorel.
Variable R : realType.
Local Notation plane := (R * R)%type.
Local Notation KR := (@compactly_supported_continuous_functions R R).

(** Source for [section_measure_measurable]: if
    phi(S) = L1[{t : S(t, 0)} cap [0, 1]] for every S and
    {t : S(t, 0)} is L1 measurable, then S is phi measurable, Federer
    2.5.4(2), p. 96, with the measurability of 2.1.2, p. 54. *)
Lemma section_measure_measurable (phi : set plane -> \bar R) (L1 : set R -> \bar R) (S : set plane) :
  (forall T : set plane, phi T = L1 ([set t | T (t, 0)] `&` `[0, 1])) ->
  measure_measurable L1 [set t | S (t, 0)] -> measure_measurable phi S.
Proof.
move=> hval hS T; rewrite !hval (hS ([set t | T (t, 0)] `&` `[0, 1])).
congr (L1 _ + L1 _); apply/seteqP; split=> t /=.
- by move=> [[hT h01] hSt]; split.
- by move=> [[hT hSt] h01]; split.
- by move=> [[hT h01] hSt]; split.
- by move=> [[hT hSt] h01]; split.
Qed.

(** Source for [plane_continuous_borel_measurable]: every Borel subset
    of R^2 is measurable for every L_2 regular measure phi_2 representing
    lambda_2, Federer 2.5.4(2), p. 96. *)
Theorem plane_continuous_borel_measurable (phi : set plane -> \bar R) :
  is_measure phi -> is_real_integral_functional phi (@plane_continuous_lattice R) (@plane_section_integral R) ->
  is_function_lattice_regular (@plane_continuous_lattice R) phi ->
  forall S : set plane, borel_set S -> measure_measurable phi S.
Proof.
move=> hm hA hr S hS.
have [L1 [hm1 [hr1 [hA1 _]]]] := @lebesgue_line_measure_exists R.
have hval := plane_continuous_regular_measure_value hm hA hr hm1 hr1 hA1.
have [_ hbor] := real_line_regular_radon hm1 hA1 hr1.
apply: (section_measure_measurable hval).
apply: (borel_regular_borel_measurable hm1 hbor).
exact: (continuous_borel_preimage (@section_map_continuous R) hS).
Qed.

End PlaneBorel.
