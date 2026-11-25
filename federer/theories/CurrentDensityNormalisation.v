(** Federer (1969), 4.1.7, p. 358:
    compare the mass-density representation with
    the bounded scalar multiple of the variation
    density. This auxiliary normalized field uses
    the original finite norm normalization of
    1.10.5, pp. 47–48; it does not redefine
    Federer's maximal orienting field. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealNormNormalization RealMetricBackground
  GrassmannAbbreviations ExteriorGrading CurrentCoefficientNorms CurrentVectorSpaces CurrentMultivectorDual
  OpenFamilyTopologyMathcomp CurrentDensityNormMeasurable RealTotalMeasurabilityProjection
  PartialFunctionBasic MeasureUP MeasurableFunctionUP MeasurableTotalBasic BorelFunctionBasic
  RealReciprocalBorel MeasurableScalarVectorProduct FiniteNormMetricPolish VectorDaniellHypotheses.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_density_normalisation_exists]:
    an auxiliary original weakly measurable field
    has mass at most one, reconstructs xi after
    multiplication by mass(xi), and has mass one
    wherever xi has nonzero mass. This supports
    Federer 4.1.7, p. 358, using 1.10.5.
    No value of the original ball-limit orientation
    is assigned by this construction. *)
Theorem current_density_normalisation_exists (R:realType) (h2:(1+1:R)!=0) n m (B:choiceType)
    (mu:set B->\bar R) (hm:is_measure mu) (xi:B->exterior_power (R_n R n) m):
  is_measure_measurable_function mu
    (partial_function_total (fun x=>(xi x:open_family_topological_space
      (@current_multivector_weak_laws R n m).1))) ->
  exists w:B->exterior_power (R_n R n) m,
    is_measure_measurable_function mu
      (partial_function_total (fun x=>(w x:open_family_topological_space
        (@current_multivector_weak_laws R n m).1))) /\
    (forall x,@current_vector_mass R h2 n m (w x)<=1) /\
    (forall x,@current_vector_mass R h2 n m (xi x)*:w x=xi x) /\
    forall x,@current_vector_mass R h2 n m (xi x)!=0 ->@current_vector_mass R h2 n m (w x) = 1.
Proof.
move=>hXi.
pose V:=exterior_power (R_n R n) m.
pose VN:=@current_vector_mass R h2 n m.
pose hVN:=@current_vector_mass_real_norm R h2 n m.
pose w x:=@real_norm_normalize R V VN (xi x).
have hXiNorm:=@current_density_mass_topology_measurable R h2 n m B mu hm xi hXi.
have hMass:=@current_density_mass_measurable R h2 n m B mu hm xi hXi.
have hMassReal:=@real_total_measurability_projection R B mu hm (fun x=>VN (xi x)) hMass.
have hInverse:=@measurable_total_borel_postcomposition R B (real_line_metric R) (real_line_metric R)
  mu hm (fun x=>VN (xi x)) (fun r=>r^-1) hMassReal (@real_reciprocal_borel R).
have [d [e he]]:=@current_vector_finite_basis R h2 n m.
have hSep:=@finite_norm_metric_separable R V VN hVN d e he.
have hWNorm:=@measurable_scalar_vector_product R B V VN hVN mu hm
  (fun x=>(VN (xi x))^-1) xi hSep hInverse hXiNorm.
have hW:=@current_density_weak_topology_measurable R h2 n m B mu hm w hWNorm.
exists w; split; first exact:hW.
split.
- move=>x; exact:(@real_norm_normalize_unit R V VN hVN.1 (xi x)).
- split.
  + move=>x; exact:(@real_norm_normalize_reconstruct R V VN hVN.2 (xi x)).
  + move=>x hx.
    have hNonzero:VN (xi x)!=0:=hx.
    have hValue:=@real_norm_normalize_value R V VN hVN.1 (xi x).
    rewrite (negbTE hNonzero) in hValue.
    exact:hValue.
Qed.
