(** Federer (1969), corrected 3.4.12, p. 339, extending 3.4.8(11), p. 327:
    a stratification at a smaller dimension bound
    also satisfies every law at a larger bound.
    The actual strata, neighbourhoods and holomorphic
    boundary varieties remain the same. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness SetGermUP HolomorphicFiniteStratificationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_stratification_dimension_bound]:
    the smaller-dimensional induction families fit
    the common original bound m in
    corrected 3.4.12, p. 339, extending 3.4.8(11), p. 327. *)
Theorem holomorphic_stratification_dimension_bound (R:realType) n
    (alpha beta:@set_germ_space
      (Topological.clone (real_norm_metric_space (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) _) 0)
    m M (U0 S0:set (coordinate_space (ComplexScalars.C R) n)) mu (V S G:'I_mu->set (coordinate_space (ComplexScalars.C R) n)):
  @is_holomorphic_finite_stratification R n alpha beta m U0 S0 mu V S G ->
  (m<=M)%N ->
  @is_holomorphic_finite_stratification R n alpha beta M U0 S0 mu V S G.
Proof.
move=>hStrat hBound;constructor.
- exact:holomorphic_stratification_neighbourhoods hStrat.
- exact:holomorphic_stratification_germ hStrat.
- move=>i;have [d [hD hFunctional]]:=holomorphic_stratification_functional hStrat i.
  exists d;split;[exact:leq_trans hD hBound|exact:hFunctional].
- exact:holomorphic_stratification_components hStrat.
- exact:holomorphic_stratification_disjoint hStrat.
- exact:holomorphic_stratification_boundary hStrat.
- exact:holomorphic_stratification_boundary_holomorphic hStrat.
- move=>i;have [hEmpty|hDimension]:=holomorphic_stratification_boundary_dimension hStrat i.
  + by left.
  + right;exact:leq_trans hDimension hBound.
- exact:holomorphic_stratification_boundary_earlier hStrat.
Qed.
