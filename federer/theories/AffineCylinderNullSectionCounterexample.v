(** Local regression supporting Federer (1969), 2.10.46, p. 204, and the
    fibre step of Freilich (1950), Theorem 4.5, Part 4, pp. 245–247. A
    scalar null factor alone does not make every individual projected fibre
    integral zero. The shear (t,x) maps to (t+x,tt); on {0} times [0,1] it
    has multiplicity one over [0,1]. The transverse fibre is infinite. This
    is a counterexample to dropping the auxiliary finite-fibre hypothesis,
    not to either author's product theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals
  constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionBasic
  MeasureUP MeasureBasic MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureCharacteristicIntegral
  CharacteristicFunctionUP CharacteristicFunctionSealed MappingMultiplicity CountingMeasure CountingInjectionBound
  TopologicalBorel BorelRegularMeasureUP LebesgueScalarMeasure ScalarLebesgueBallContext IntervalBumpFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [sheared_null_line_fibre_count]: local
    counterexample calculation supporting 2.10.46, p. 204.
    A singleton scalar factor may give one point in every
    fibre of a scalar shear over a nontrivial interval. *)
Lemma sheared_null_line_fibre_count (R : realType) (w : R) :
  @mapping_multiplicity R [the choiceType of (R*R)%type] (R*unit)%type
    (fun z=>((z.1+z.2)%R,tt)) ([set 0%R] `*` `[0%R,1%R]) (w,tt)=
    (@CharacteristicFunction.value R R `[0%R,1%R] w)%:E.
Proof.
case: (pselect ((`[0%R,1%R] : set R) w))=> hw.
- have he : mapping_fibre (fun z : R*R=>((z.1+z.2)%R,tt))
      ([set 0%R] `*` `[0%R,1%R]) (w,tt)=[set (0%R,w)].
    apply/seteqP; split=> z.
    + case: z=> t x [[ht hx] he]; change (t=0%R) in ht; subst t.
      have hh := congr1 fst he; change ((0+x)%R=w) in hh; rewrite add0r in hh; by subst x.
    + move=> ->; split; first by split.
      by rewrite /= add0r.
  by rewrite /mapping_multiplicity he counting_measure_singleton_value
    (characteristic_on_set (CharacteristicFunction.laws R `[0%R,1%R]) hw).
- have he : mapping_fibre (fun z : R*R=>((z.1+z.2)%R,tt))
      ([set 0%R] `*` `[0%R,1%R]) (w,tt)=set0.
    apply/seteqP; split=> z //; case: z=> t x [[ht hx] he].
    change (t=0%R) in ht; subst t; have hh := congr1 fst he.
    change ((0+x)%R=w) in hh; rewrite add0r in hh; subst x; exact: hw hx.
  by rewrite /mapping_multiplicity he (measure_empty (counting_measure_is_measure R [the choiceType of (R*R)%type]))
    (characteristic_off_set (CharacteristicFunction.laws R `[0%R,1%R]) hw).
Qed.

(** Source for [null_scalar_infinite_fibre_counterexample]: local
    regression for 2.10.46, p. 204, guarding the
    finite-fibre qualification in the null-factor case. The
    scalar factor has measure zero, the transverse fibre has
    infinite count, and the shear's scalar multiplicity integral
    nevertheless equals one. No correction to Federer is asserted. *)
Theorem null_scalar_infinite_fibre_counterexample (R : realType) :
  lebesgue_scalar_measure [set (0%R : R)]=0 /\
  @counting_measure R R `[0%R,1%R]=+oo /\
  is_measure_integral (@lebesgue_scalar_measure R) (partial_function_total
    (fun w=>(@mapping_multiplicity R [the choiceType of (R*R)%type] (R*unit)%type
      (fun z=>((z.1+z.2)%R,tt)) ([set 0%R] `*` `[0%R,1%R]) (w,tt) : extended_real_line R))) 1.
Proof.
split; first exact: lebesgue_scalar_singleton.
split.
- apply: counting_measure_infinite=> hf.
  have hz := @scalar_lebesgue_countable_null R `[0%R,1%R] (finite_set_countable hf).
  rewrite lebesgue_scalar_segment ?ler01 // subr0 in hz.
  have he : ((1 : \bar R)==0) by apply/eqP; exact hz.
  by rewrite eqe oner_eq0 in he.
- have hB : @borel_set [the topologicalType of real_line_metric R] `[0%R,1%R].
    apply: closed_borel_set; exact: segment_closed_real.
  have hM := @borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
    (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) (lebesgue_scalar_borel_regular R) _ hB.
  have hi := @measure_characteristic_integral R [the choiceType of real_line_metric R]
    (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) `[0%R,1%R]
    (@CharacteristicFunction.value R R `[0%R,1%R]) (CharacteristicFunction.laws R _) hM.
  rewrite lebesgue_scalar_segment ?ler01 // subr0 in hi.
  apply: (@measure_integral_graph_equivalent R [the choiceType of real_line_metric R]
    (@lebesgue_scalar_measure R) _ _ 1 _ hi)=> w z.
  change ((exists r : R, CharacteristicFunction.value R `[0%R,1%R] w=r /\ r%:E=z) <->
    @mapping_multiplicity R [the choiceType of (R*R)%type] (R*unit)%type
      (fun z=>((z.1+z.2)%R,tt)) ([set 0%R] `*` `[0%R,1%R]) (w,tt)=z).
  rewrite sheared_null_line_fibre_count; split; first by move=> [r [<- hz]].
  move=> hz; exists (CharacteristicFunction.value R `[0%R,1%R] w); by split.
Qed.
