(** Supporting Federer (1969), 2.10.46, p. 204: the finite-fibre integral in
    Freilich (1950), Theorem 4.5, Part 4, pp. 245–247. Integrate the actual
    number of shifted scalar sections, keeping overlaps with their
    multiplicity. Their common affine-image measure yields the fibre count
    times the scalar stretching factor times the scalar measure. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionBasic
  MeasureUP MeasureBasic MeasureIntegralUP CountingMeasure TopologicalBorel BorelRegularMeasureUP
  LebesgueScalarMeasure ScalarAffineSections FiniteSectionCountingIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_affine_cylinder_section_integral]: supporting
    finite multiplicity calculation for 2.10.46, p. 204;
    Freilich (1950), Theorem 4.5, Part 4,
    pp. 245–247. The scalar set is Borel of
    finite measure. Empty fibres and scalar null sets are included;
    the stretching factor must be nonzero. *)
Theorem finite_affine_cylinder_section_integral (R : realType) (J : choiceType)
    (F : {fset J}) (T : set (real_line_metric R)) (a ell : R) (b : J -> R) :
  a!=0%R -> borel_set T -> lebesgue_scalar_measure T=ell%:E ->
  is_measure_integral (@lebesgue_scalar_measure R) (partial_function_total
    (fun w=>(counting_measure (R:=R) [set j | j \in F /\ T ((w-b j)/a)%R] : extended_real_line R)))
    ((`|a|*ell)%R%:E*counting_measure (R:=R) [set` F]).
Proof.
move=> ha hT hell.
have hm := lebesgue_scalar_is_measure R.
have he0 : (0<=ell)%R.
  have hh := measure_nonnegative hm T; by rewrite hell lee_fin in hh.
apply: (@finite_equal_section_count_integral R [the choiceType of real_line_metric R] J
  (@lebesgue_scalar_measure R) hm F (fun j=>[set w | T ((w-b j)/a)%R]) (`|a|*ell)%R).
- exact: mulr_ge0 (normr_ge0 a) he0.
- move=> j hj; apply: (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
    (@lebesgue_scalar_measure R) hm (lebesgue_scalar_borel_regular R)).
  exact: scalar_affine_section_borel hT.
- move=> j hj; by rewrite (@scalar_affine_section_measure R a (b j) T ha) hell EFinM.
Qed.
