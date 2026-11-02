(** Supporting Federer (1969), 2.10.46, p. 204: Freilich (1950), Theorem
    4.5, Part 4, p. 247, passes from finite to infinite fibres. Every finite
    collection of transverse points gives a lower bound for the scalar
    multiplicity integral; the counting supremum then gives the full lower
    bound. The scalar null case is not used to assert equality for an
    arbitrary infinite fibre. Source context:
    AffineCylinderSectionIntegral.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionBasic
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic PartialExtendedOrderLoci
  MeasureIntegralUP MeasureIntegralComparison MeasureIntegralUniqueness CountingMeasure CountingConstantSum
  NonnegativeSum NonnegativeSumSupport MappingMultiplicity TopologicalBorel LebesgueScalarMeasure
  AffineCylinderFibreCount AffineCylinderFiniteIntegral AffineCylinderSectionIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [affine_cylinder_section_integral_lower]: supporting
    finite-subsum lower bound for 2.10.46, p. 204;
    Freilich (1950), Theorem 4.5, Part 4,
    p. 247. Once the multiplicity integral exists,
    its value dominates the common section length times the
    transverse count, including uncountable transverse fibres. *)
Theorem affine_cylinder_section_integral_lower (R : realType) (X Y : choiceType)
    (f : R*X -> R*Y) (q : X -> Y) (a ell : R) (b : X -> R)
    (T : set (real_line_metric R)) (V : set X) (y : Y) (J : \bar R) :
  a!=0%R -> (forall t x, f (t,x)=((a*t+b x)%R,q x)) ->
  borel_set T -> lebesgue_scalar_measure T=ell%:E ->
  is_measure_integral (@lebesgue_scalar_measure R) (partial_function_total
    (fun w=>(@mapping_multiplicity R [the choiceType of (R*X)%type] (R*Y)%type
      f (T `*` V) (w,y) : extended_real_line R))) J ->
  (`|a|*ell)%R%:E*@mapping_multiplicity R X Y q V y<=J.
Proof.
move=> ha hf hT hell hi.
have hm := lebesgue_scalar_is_measure R.
have he0 : (0<=ell)%R.
  have hh := measure_nonnegative hm T; by rewrite hell lee_fin in hh.
have hc : (0<=`|a|*ell)%R := mulr_ge0 (normr_ge0 a) he0.
rewrite /mapping_multiplicity -nonnegative_constant_sum_counting //.
apply: nonnegative_sum_least=> F hF.
have hsum : (\sum_(x <- F) (`|a|*ell)%R%:E)=
    (`|a|*ell)%R%:E*counting_measure (R:=R) [set` F].
  by rewrite -nonnegative_constant_sum_counting // nonnegative_sum_finite // => x hx; rewrite lee_fin.
rewrite hsum.
have hfin := @finite_affine_cylinder_section_integral R X F T a ell b ha hT hell.
apply: (@measure_integral_monotone R [the choiceType of real_line_metric R]
  (@lebesgue_scalar_measure R) hm _ _ _ J hfin hi).
apply: (@measure_almost_everywhere_mono R [the choiceType of real_line_metric R]
  (@lebesgue_scalar_measure R) hm setT _ _ (measure_almost_everywhere_true hm))=> w _.
exists (counting_measure (R:=R) [set x | x \in F /\ T ((w-b x)/a)%R]),
  (@mapping_multiplicity R [the choiceType of (R*X)%type] (R*Y)%type f (T `*` V) (w,y)).
split=> //; split=> //.
rewrite (@affine_cylinder_fibre_count R X Y f q a b T V w y ha hf).
apply: (@measure_mono R X _ (counting_measure_is_measure R X))=> x [hx ht].
have [hv hq] := hF x hx; by split=> //; split.
Qed.

(** Source for [affine_cylinder_section_integral_value]: supporting
    complete fibre value in the cylinder argument, 2.10.46,
    p. 204; Freilich (1950), Theorem 4.5,
    Part 4, pp. 245–247. Positive scalar length
    permits infinite fibres; when the scalar length is zero,
    this lemma requires a finite transverse fibre. The eventual
    averaging argument must discharge that restriction almost everywhere. *)
Theorem affine_cylinder_section_integral_value (R : realType) (X Y : choiceType)
    (f : R*X -> R*Y) (q : X -> Y) (a ell : R) (b : X -> R)
    (T : set (real_line_metric R)) (V : set X) (y : Y) (J : \bar R) :
  a!=0%R -> (forall t x, f (t,x)=((a*t+b x)%R,q x)) ->
  borel_set T -> lebesgue_scalar_measure T=ell%:E ->
  (finite_set (mapping_fibre q V y) \/ (0<ell)%R) ->
  is_measure_integral (@lebesgue_scalar_measure R) (partial_function_total
    (fun w=>(@mapping_multiplicity R [the choiceType of (R*X)%type] (R*Y)%type
      f (T `*` V) (w,y) : extended_real_line R))) J ->
  J=(`|a|*ell)%R%:E*@mapping_multiplicity R X Y q V y.
Proof.
move=> ha hf hT hell hdom hi.
case: (pselect (finite_set (mapping_fibre q V y)))=> [hfin|hinf].
- exact: measure_integral_unique hi
    (@affine_cylinder_finite_fibre_integral R X Y f q a ell b T V y ha hf hT hell hfin).
- have hp : (0<ell)%R by case: hdom=> // hh; exfalso; exact: hinf hh.
  have hc : (0<`|a|*ell)%R by rewrite mulr_gt0 // normr_gt0.
  have hn : @mapping_multiplicity R X Y q V y=+oo.
    rewrite /mapping_multiplicity; exact: counting_measure_infinite hinf.
  have hb := @affine_cylinder_section_integral_lower R X Y f q a ell b T V y J ha hf hT hell hi.
  rewrite hn muleC gt0_mulye ?lte_fin // in hb *.
  by apply/eqP; rewrite eq_le leey hb.
Qed.
