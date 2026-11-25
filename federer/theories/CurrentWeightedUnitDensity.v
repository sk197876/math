(** Federer (1969), 4.1.7, pp. 358–359:
    normalize an actual multivector density
    with respect to its original mass-weighted
    measure. This supporting source-independent form
    of the earlier normalization retains distinct
    source and coefficient dimensions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations ExteriorGrading CurrentCoefficientNorms
  CurrentMultivectorDual CurrentDensityNormalisation CurrentDensityNormMeasurable OpenFamilyTopologyMathcomp
  PartialFunctionBasic PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasureDensity MeasureDensityTransfer RealFiniteDensityIntegral SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_weighted_unit_density_exists]:
    the exact mass-weighted measure has an
    auxiliary weak density of mass one
    almost everywhere, with an everywhere unit
    bound and pointwise reconstruction of the
    original field, supporting Federer 4.1.7,
    pp. 358–359. This auxiliary witness
    does not redefine the original orientation. *)
Theorem current_weighted_unit_density_exists (R:realType) (h2:(1+1:R)!=0) n m (B:choiceType)
    (mu:set B->\bar R) (hm:is_measure mu) (xi:B->exterior_power (R_n R n) m):
  is_measure_measurable_function mu
    (partial_function_total (fun x=>(xi x:open_family_topological_space
      (@current_multivector_weak_laws R n m).1)))->
  exists w:B->exterior_power (R_n R n) m,
    is_measure_measurable_function mu
      (partial_function_total (fun x=>(w x:open_family_topological_space
        (@current_multivector_weak_laws R n m).1))) /\
    is_measure_measurable_function
      (measure_with_density mu (real_total_integrand (fun x=>@current_vector_mass R h2 n m (xi x))))
      (partial_function_total (fun x=>(w x:open_family_topological_space
        (@current_multivector_weak_laws R n m).1))) /\
    (forall x,@current_vector_mass R h2 n m (w x)<=1) /\
    (forall x,@current_vector_mass R h2 n m (xi x)*:w x=xi x) /\
    measure_almost_everywhere
      (measure_with_density mu (real_total_integrand (fun x=>@current_vector_mass R h2 n m (xi x))))
      [set x|@current_vector_mass R h2 n m (w x) = 1].
Proof.
move=>hXi.
pose V:=exterior_power (R_n R n) m.
pose N:=@current_vector_mass R h2 n m.
pose H:=real_total_integrand (fun x=>N (xi x)).
pose lambda:=measure_with_density mu H.
have [w [hW [hUnit [hReconstruct hUnitNonzero]]]]:=
  @current_density_normalisation_exists R h2 n m B mu hm xi hXi.
have hPositive:measure_almost_everywhere mu (partial_extended_nonnegative_locus H).
  apply:(@measure_almost_everywhere_mono R B mu hm setT _ _
    (measure_almost_everywhere_true hm))=>x _.
  exists (N (xi x))%:E;split;first by rewrite real_total_integrand_graph.
  rewrite lee_fin;exact:real_seminorm_nonnegative (@current_vector_mass_real_norm R h2 n m).1 _.
have hLambda:=@measure_with_density_is_measure R B mu hm H hPositive.
have hWeakLambda:=@measure_density_measurable_function R B
  (open_family_topological_space (@current_multivector_weak_laws R n m).1) mu lambda hm H
  (partial_function_total (fun x=>(w x:open_family_topological_space
    (@current_multivector_weak_laws R n m).1))) (measure_with_density_laws mu H) hPositive hW.
have hZero:=@finite_real_density_zero_locus_null R B mu lambda hm (fun x=>N (xi x))
  (measure_with_density_laws mu H).
have hOne:measure_almost_everywhere lambda [set x|N (w x) = 1].
  apply:(@measure_null_subset R B lambda hLambda _ _ _ hZero)=>x hx.
  case:(eqVneq (N (xi x)) 0)=>h;first exact:h.
  exfalso;exact:hx (hUnitNonzero x h).
exists w;split;first exact:hW.
split;first exact:hWeakLambda.
split;first exact:hUnit.
split;[exact:hReconstruct|exact:hOne].
Qed.
