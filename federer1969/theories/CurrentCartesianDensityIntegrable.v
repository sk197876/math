(** Federer (1969), 4.1.8, p. 361: the original
    product-density coefficient is locally mass-integrable.
    Use the actual Radon product and the existing finite
    coefficient bound. No total-mass or new pointwise
    regularity premise is imposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading EuclideanCartesianMap
  CurrentDomain CurrentCoefficientNorms CurrentMultivectorDual CurrentMeasurableProductCoefficients
  CurrentCartesianDomainMapsSealed CurrentCartesianMeasureSealed CurrentCartesianMeasureRadon
  CurrentCartesianVectorProduct CurrentCartesianDensityMeasurable OpenCurrentDensityUP
  OpenFamilyTopologyMathcomp PartialFunctionBasic MeasureUP RadonMeasureUP RadonBorelRegularity
  MeasurableFunctionUP MeasureSubsetIntegral SummableRealFunctionUP NormBoundedBilinearUP
  BoundedVectorNormSubsetIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianDensityIntegrable.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Hypothesis hA:forall a,A a->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AT := (current_domain R m A).
Local Notation BT := (current_domain R n B).
Local Notation CT := (current_domain R (m+n) (@euclidean_cartesian_set R m n A B)).
Local Notation D := (@CartesianCurrentDomain.split R m n A B).
Local Notation VA := (exterior_power (R_n R m) i).
Local Notation VB := (exterior_power (R_n R n) j).
Local Notation VC := (exterior_power (R_n R (m+n)) (i+j)).
Local Notation NA := (@current_vector_mass R h2 m i).
Local Notation NB := (@current_vector_mass R h2 n j).
Local Notation NC := (@current_vector_mass R h2 (m+n) (i+j)).
Local Notation hNC := (@current_vector_mass_real_norm R h2 (m+n) (i+j)).
Local Notation WA := (open_family_topological_space (@current_multivector_weak_laws R m i).1).
Local Notation WB := (open_family_topological_space (@current_multivector_weak_laws R n j).1).
Local Notation F := (@current_cartesian_vector_product R m n i j).
Variables (alpha:set AT->\bar R) (beta:set BT->\bar R).
Hypothesis hAlpha:is_measure alpha.
Hypothesis hBeta:is_measure beta.
Hypothesis hRA:is_radon_measure alpha.
Hypothesis hRB:is_radon_measure beta.
Local Notation lambda := (@CartesianCurrentMeasure.value R m n A B alpha beta hAlpha hBeta).
Local Notation hm := (@current_cartesian_measure_is_measure R m n A B alpha beta hAlpha hBeta).
Variables (xi:AT->VA) (eta:BT->VB).
Hypothesis hXi:is_measure_measurable_function alpha (partial_function_total (fun x=>(xi x:WA))).
Hypothesis hEta:is_measure_measurable_function beta (partial_function_total (fun x=>(eta x:WB))).
Hypothesis hUnitXi:forall x,NA (xi x)<=1.
Hypothesis hUnitEta:forall x,NB (eta x)<=1.
Local Notation zeta := (@current_cartesian_density R m n i j A B xi eta).

(** Source for [current_cartesian_density_locally_integrable]:
    the original product-density coefficient satisfies the
    complete local input conditions for the Radon current,
    supporting Federer 4.1.8, p. 361. The factors have
    their original unit-bounded normalized densities. *)
Theorem current_cartesian_density_locally_integrable:
  @is_locally_integrable_open_current_density R h2 (m+n) (i+j)
    (@euclidean_cartesian_set R m n A B) lambda zeta.
Proof.
have hNormMeas:=@current_cartesian_density_norm_measurable R h2 m n i j A B xi eta
  alpha beta hAlpha hBeta hXi hEta.
split.
- exact:(@current_cartesian_density_weak_measurable R h2 m n i j A B xi eta
    alpha beta hAlpha hBeta hXi hEta).
- move=>K hK.
  have hRadon:=@current_cartesian_measure_radon R m n A B hA hB alpha beta hAlpha hBeta hRA hRB.
  have hFinite:=radon_compact_finite hRadon hK.
  have hNum:lambda K \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hm K)).
  have hValue:lambda K=(fine (lambda K))%:E by rewrite fineK.
  have[C [hC hBound]]:=(@current_cartesian_vector_product_bounded R h2 m n i j).2.
  have hGlobal:forall x,NC (zeta x)<=C.
    move=>x;apply:le_trans (hBound _ _) _.
    have hProduct:NA (xi (D x).1)*NB (eta (D x).2)<=1.
      apply:le_trans (ler_wpM2r (real_seminorm_nonnegative
        (@current_vector_mass_real_norm R h2 n j).1 _) (hUnitXi (D x).1)) _.
      by rewrite mul1r;exact:hUnitEta.
    have h:=ler_wpM2l hC hProduct;by rewrite mulr1 in h.
  have[E [hEC hED]]:=@current_vector_coefficient_separable R h2 (m+n) (i+j).
  exact:(@bounded_vector_norm_subset_integral R CT VC NC hNC E lambda hm K
    (fine (lambda K)) C zeta hEC hED (radon_compact_measurable hm hRadon hK)
    hValue hNormMeas hGlobal).
Qed.
End CurrentCartesianDensityIntegrable.
