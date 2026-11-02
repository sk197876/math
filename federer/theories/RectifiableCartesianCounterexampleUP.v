(** Federer (1969), 3.2.24, p. 260: independent counterexample
    laws. The two factor dimensions are two and the ambient dimensions
    are four. The printed example is existential; these concrete
    dimensions are supplied by the fourth Cantor powers of 2.10.29. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanCartesianMap RectifiableSetUP HausdorffMeasure TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_rectifiable_cartesian_counterexample]: the
    zero factor masses and infinite product mass of Federer 3.2.24,
    p. 260. The finite-mass measure rectifiability of the two
    factors and their Borel property are retained explicitly. *)
Record is_rectifiable_cartesian_counterexample (R:realType)
    (W Z:set (R_n R 4)):Prop:={
  (** Source for [cartesian_counterexample_borel]: the Cantor powers
      in 2.10.29, p. 195, provide Borel factors for the failure
      described in 3.2.24, p. 260. *)
  cartesian_counterexample_borel:
    @borel_set (inner_metric_space (@euclidean_inner_productP R 4)) W /\
    @borel_set (inner_metric_space (@euclidean_inner_productP R 4)) Z;
  (** Source for [cartesian_counterexample_factor_null]: the equations
      H^m(W)=H^mu(Z)=0 in 3.2.24, p. 260, here m=mu=2. *)
  cartesian_counterexample_factor_null:
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 4)) 2 W=0 /\
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 4)) 2 Z=0;
  (** Source for [cartesian_counterexample_factor_rectifiability]: both
      factors are (H^2,2) rectifiable, as required for the proposed
      weakened hypothesis in 3.2.24, p. 260. *)
  cartesian_counterexample_factor_rectifiability:
    is_measure_m_rectifiable (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R 4)) 2) 2 W /\
    is_measure_m_rectifiable (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R 4)) 2) 2 Z;
  (** Source for [cartesian_counterexample_product_infinite]: the equation
      H^(m+mu)(W times Z)=infinity in 3.2.24, p. 260,
      under the usual Euclidean block identification. *)
  cartesian_counterexample_product_infinite:
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (4+4))) (2+2)
      (euclidean_cartesian_set W Z)=+oo
}.
