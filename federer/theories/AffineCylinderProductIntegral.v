(** Supporting Federer (1969), 2.10.46, p. 204: the first Fubini passage in
    Freilich (1950), Theorem 4.5, Parts 1, 4 and 5, pp. 242–247. The affine
    coordinate formula and almost-everywhere finite transverse fibres
    identify the product multiplicity integral. Both integrals are supplied
    as actual integral statements, with their measurability obligations
    explicit. The projection application must establish these obligations
    and the later rotation average; this is not the final I_1 identity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals
  constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialProductSections PartialExtendedOrderLoci MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  MeasureIntegralAlmostEquality ProductMeasure ProductFunctionFubini ParameterizedIntegral
  CountablyMeasurableUP CountablyMeasurableFunctions MappingMultiplicity TopologicalBorel LebesgueScalarMeasure
  TotalNonnegativeExtendedScaleIntegral AffineCylinderSectionIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [affine_cylinder_product_integral_value]: supporting
    product integral step for 2.10.46, p. 204;
    Freilich (1950), Theorem 4.5, Part 5,
    p. 247, using Fubini from Part 1,
    pp. 242–243. Finite scalar and transverse integral
    values include zero. Exceptional infinite fibres are discarded
    only after an explicit almost-everywhere finiteness proof. *)
Theorem affine_cylinder_product_integral_value (R : realType) (X Y : choiceType)
    (beta : set Y -> \bar R) (hb : is_measure beta)
    (f : R*X -> R*Y) (q : X -> Y) (a ell r : R) (b : X -> R)
    (T : set (real_line_metric R)) (V : set X) (J : \bar R) :
  a!=0%R -> (forall t x, f (t,x)=((a*t+b x)%R,q x)) ->
  borel_set T -> lebesgue_scalar_measure T=ell%:E ->
  measure_almost_everywhere beta [set y | finite_set (mapping_fibre q V y)] ->
  is_measure_integral beta (partial_function_total
    (fun y=>(@mapping_multiplicity R X Y q V y : extended_real_line R))) r%:E ->
  is_measure_integral (product_measure (lebesgue_scalar_is_measure R) hb)
    (partial_function_total (fun z=>(@mapping_multiplicity R [the choiceType of (R*X)%type]
      (R*Y)%type f (T `*` V) z : extended_real_line R))) J ->
  is_countably_measure_measurable_function (product_measure (lebesgue_scalar_is_measure R) hb)
    (0 : extended_real_line R) (partial_function_total
      (fun z=>(@mapping_multiplicity R [the choiceType of (R*X)%type]
        (R*Y)%type f (T `*` V) z : extended_real_line R))) ->
  J=(`|a|*ell*r)%R%:E.
Proof.
move=> ha hf hT hell hfinite hq hj hcount.
pose g := partial_function_total (fun z=>(@mapping_multiplicity R [the choiceType of (R*X)%type]
  (R*Y)%type f (T `*` V) z : extended_real_line R)).
pose h := parameterized_integral (@lebesgue_scalar_measure R) (partial_product_horizontal_section g).
have ho := (@product_function_fubini R [the choiceType of real_line_metric R] Y
  (@lebesgue_scalar_measure R) beta (lebesgue_scalar_is_measure R) hb g J hj hcount).2.
have hdom : measure_almost_everywhere beta (partial_function_domain h) := measurable_function_domain ho.1.
have hgood := @measure_almost_everywhere_and R Y beta hb _ _ hfinite hdom.
pose c : R := (`|a|*ell)%R.
pose v y := (c%:E*@mapping_multiplicity R X Y q V y : extended_real_line R).
have he : measure_almost_equal beta h (partial_function_total v).
  apply: (@measure_almost_everywhere_mono R Y beta hb _ _ _ hgood)=> y [hy [s hs]].
  have his := (parameterized_integral_specification (@lebesgue_scalar_measure R)
    (partial_product_horizontal_section g) y s).1 hs.
  have hfib := @affine_cylinder_finite_fibre_integral R X Y f q a ell b T V y ha hf hT hell hy.
  have hsec : is_measure_integral (@lebesgue_scalar_measure R)
      (partial_product_horizontal_section g y) (v y).
    apply: (@measure_integral_graph_equivalent R [the choiceType of real_line_metric R]
      (@lebesgue_scalar_measure R) _ _ (v y) _ hfib)=> w z; by [].
  have hv := measure_integral_unique his hsec.
  exists s; split=> //; change (v y=s); exact: esym hv.
have hov := @measure_integral_almost_equal R Y beta hb h (partial_function_total v) J ho he.
have hell0 : (0<=ell)%R.
  have hh := measure_nonnegative (lebesgue_scalar_is_measure R) T; by rewrite hell lee_fin in hh.
have hc : 0<=c%:E by rewrite lee_fin; exact: mulr_ge0 (normr_ge0 a) hell0.
have hv := @total_nonnegative_extended_scale_integral R Y beta hb
  (fun y=>(@mapping_multiplicity R X Y q V y : extended_real_line R)) r%:E c%:E
  (fun y=>@mapping_multiplicity_nonnegative R X Y q V y) hq hc.
have heJ := measure_integral_unique hov hv.
by rewrite heJ /c -EFinM.
Qed.
