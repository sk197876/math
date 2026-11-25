(** Federer (1969), 4.1.8, p. 362: the constant
    velocity multivector is locally integrable for the
    original Radon parameter image. This supporting
    arbitrary-open input check reuses the existing
    bounded-vector subset integral theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct ExteriorGrading CurrentDomain CurrentCoefficientNorms CurrentMultivectorDual
  CurrentMeasurableProductCoefficients OpenCurrentDensityUP OpenFamilyTopologyMathcomp
  PartialFunctionBasic MeasurableFunctionUP MeasurableTotalBasic MeasureUP RadonMeasureUP
  RadonBorelRegularity BoundedVectorNormSubsetIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_constant_radon_density_integrable]:
    every original constant multivector field is weakly
    measurable and locally mass-integrable for Radon gamma,
    supporting Federer 4.1.8, p. 362, through the
    actual density-current theorem of 4.1.7. *)
Theorem current_constant_radon_density_integrable (R:realType) (h2:(1+1:R)!=0) n m
    (A:set (R_n R n)) (gamma:set (current_domain R n A)->\bar R)
    (hGamma:is_measure gamma) (hRadon:is_radon_measure gamma)
    (a:exterior_power (R_n R n) m):
  @is_locally_integrable_open_current_density R h2 n m A gamma (fun _=>a).
Proof.
split.
- exact:(@measurable_total_constant R (current_domain R n A)
    (open_family_topological_space (@current_multivector_weak_laws R n m).1)
    gamma hGamma a).
- move=>K hK.
  have hFinite:=radon_compact_finite hRadon hK.
  have hNum:gamma K \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hGamma K)).
  have hValue:gamma K=(fine (gamma K))%:E by rewrite fineK.
  have[E [hEC hED]]:=@current_vector_coefficient_separable R h2 n m.
  have hMeas:=@measurable_total_constant R (current_domain R n A)
    (real_norm_metric_space (@current_vector_mass_real_norm R h2 n m)) gamma hGamma a.
  exact:(@bounded_vector_norm_subset_integral R (current_domain R n A)
    (exterior_power (R_n R n) m) (@current_vector_mass R h2 n m)
    (@current_vector_mass_real_norm R h2 n m) E gamma hGamma K (fine (gamma K))
    (@current_vector_mass R h2 n m a) (fun _=>a) hEC hED
    (radon_compact_measurable hGamma hRadon hK) hValue hMeas (fun _=>lexx _)).
Qed.
