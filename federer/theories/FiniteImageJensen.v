(** Federer (1969), 2.4.19, p. 91: Jensen's inequality for finite-image
    functions. This is the first case of both printed proofs. Only the
    defining vector-integral laws and characteristic fibre integrals are
    used; Banach completeness and continuity of F are unnecessary in this
    finite case. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPostcomposition
  MeasureUP MeasureBasic MeasureStepFunctionUP MeasureIntegralUP MeasureIntegralUniqueness MeasureVectorIntegralUP
  ConvexFunctionUP ConvexEpigraph FiniteFibreMass FiniteVectorIntegralFormula FiniteScalarIntegralFormula.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_image_jensen]: direct finite-image case of Federer
    2.4.19, p. 91 The conclusion includes membership of the mean in C.
    Partial domains are allowed; all defined values lie in C in this
    preparatory version, before removing null exceptions. *)
Theorem finite_image_jensen (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (m : R)
    (C : set V) (F : V -> R) (f : partial_function X (real_norm_metric_space hN)) (y : V) (a : \bar R) :
  mu setT=m%:E -> (0 < m)%R -> is_real_convex_function_on C F ->
  (forall z, C z -> (0 <= F z)%R) ->
  finite_set (partial_function_range f) -> (forall z, partial_function_range f z -> C z) ->
  is_measure_vector_integral mu f y ->
  is_measure_integral mu (partial_function_postcompose f (fun z => ((F z)%:E : extended_real_line R))) a ->
  C ((m^-1)%R *: y)%R /\ (F ((m^-1)%R *: y)%R)%:E <= a * (m^-1)%R%:E.
Proof.
move=> hmass hm0 hF hpos hfin hrange hy ha.
pose S := fset_set (partial_function_range f).
pose b z := fine (mu (partial_function_preimage f [set z])).
have hf := hy.1.2.1.1.
have hmu : mu setT < +oo by rewrite hmass ltry.
have hb z : (0 <= b z)%R.
  have hfinite := (@finite_source_function_fibre R X V N hN mu hm f z hmu hf).2.
  have he : mu (partial_function_preimage f [set z])=(b z)%:E by rewrite /b fineK.
  have hnon := measure_nonnegative hm (partial_function_preimage f [set z]).
  by rewrite he lee_fin in hnon.
have hmem z : z \in S -> partial_function_range f z.
  by rewrite /S in_fset_set //; exact: set_mem.
have hsum := @finite_fibre_mass_sum R X V N hN mu hm f m hmass hf hfin.
have hj := @finite_mass_normalized_jensen R V C F (S : seq V) b m hF
  (fun z hz => hrange z (hmem z hz)) (fun z _ => hb z) hm0 hsum.
have hy' := @finite_vector_integral_fibre_formula R X V N hN mu hm f hy.1 hfin.
have hay := measure_vector_integral_unique hy hy'.
have ha' := @finite_scalar_composite_integral_formula R X V N hN mu hm f F hmu hf hfin
  (fun z hz => hpos z (hrange z hz)).
have haa := measure_integral_unique ha ha'.
rewrite hay haa; split; first exact hj.1.
rewrite -EFinM lee_fin.
have he : (\sum_(z <- S) F z * b z)%R=(\sum_(z <- S) b z * F z)%R.
  apply: eq_bigr=> z _; exact: mulrC.
change ((F ((m^-1)%R *: (\sum_(z <- S) b z *: z)) <=
  (\sum_(z <- S) F z * b z) * m^-1)%R).
rewrite he; exact hj.2.
Qed.
