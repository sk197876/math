(** Federer (1969), 4.1.18, p. 376: original L1
    convergence of the coefficients gives weak convergence
    of their actual Lebesgue currents. The original mass
    identity and mass-to-test convergence prove this directly. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Bilinear Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading CurrentDomain CurrentSpaces CurrentCoefficientNorms
  CurrentMassSealed CurrentMassWeakConvergence CurrentWeakSequenceLimit
  CompactSummableMultivectors CompactSummableMultivectorDensity
  CompactSummableMultivectorLinear CompactSummableFieldFinitePrefix
  CompactSummableFieldLaws EuclideanOpenDomainMeasure
  PartialFunctionBasic MeasureLpConvergence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section WeakLimit.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation W:=(@compact_summable_multivector_space R h2 n m U hU).
Local Notation value:=(@compact_summable_multivector_value R h2 n m U hU).
Local Notation size:=(@compact_summable_multivector_size R h2 n m U hU).
Local Notation D:=(@compact_summable_multivector_current_hom R h2 n m U hU).
Local Notation VN:=(@current_vector_mass R h2 n m).
Local Notation hVN:=(@current_vector_mass_real_norm R h2 n m).
Local Notation mu:=(@euclidean_open_domain_measure R n U).
Local Notation hm:=(proj1 (@euclidean_open_domain_measure_laws R n U hU)).

(** Source for [current_lone_field_weak_limit]: the actual
    integral currents of the L1 coefficient prefixes have
    the claimed original weak limit, Federer 4.1.18, p. 376.
    Neither smoothness nor one common support is needed
    for this supporting implication. *)
Theorem current_lone_field_weak_limit (u:nat->W) (w:W):
  converges_in_lp_norm mu VN 1
    (fun k=>partial_function_total (value (u k)))
    (partial_function_total (value w))->
  @is_current_weak_sequence_limit R h2 n m U hU (fun k=>D (u k)) (D w).
Proof.
move=>hLone.
apply:(@current_mass_convergence_is_weak R h2 n m U hU
  (fun k=>D (u k)) (D w))=>epsilon hEpsilon.
have[k hk]:=hLone epsilon hEpsilon.
exists k=>j hj.
have h:=hk j hj.
rewrite (@compact_summable_field_distance R (current_domain R n U)
  (exterior_power (R_n R n) m) VN hVN mu hm) in h.
rewrite -(linB (hom_linear D)).
change (@CurrentMass.value R h2 n m U hU
  (@compact_summable_multivector_current R h2 n m U hU (w-u j))<epsilon%:E)%E.
rewrite compact_summable_multivector_current_mass
  (real_seminorm_subtract (@compact_summable_multivector_size_laws R h2 n m U hU)).
exact:h.
Qed.
End WeakLimit.
