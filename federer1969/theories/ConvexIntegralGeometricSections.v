(** The original all-set Gillespie section inequality
    of Federer (1969), 3.2.45, p. 280. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates EuclideanLebesgueDimensions
  IntegralGeometricMeasure IntegralGeometricClosedCovers ConvexGeometricSectionCutoff ConvexGeometricSectionCutoffs
  MetricScaleEnvelope CaratheodoryBorelRegular ExtendedRealOrderTopology MeasureUP MeasureBasic
  PartialFunctionUP PartialFunctionBasic MeasureIntegralBounds IncreasingUpperIntegralBound.
From Federer Require Export BoundedConvexIntrinsicSectionComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_integral_geometric_section_upper_integral]: direct
    first display on p. 280 of Federer 3.2.45.
    The original closed-convex covering infima at reciprocal
    cutoffs increase to the actual Gillespie mass of
    each original section. The proved convex generator
    inequality bounds every cutoff upper integral.
    Increasing upper-integral continuity proves the literal
    upper-star assertion. A need not be measurable;
    the section function need not be measurable or
    finite. Empty blocks, degree zero and infinite
    source mass remain. *)
Theorem convex_integral_geometric_section_upper_integral (R : realType) m q k (hKQ : (k<=q)%N)
    (A : set (inner_metric_space (@euclidean_inner_productP R (m+q)))) :
  measure_upper_integral (@euclidean_lebesgue_measure R m)
    (partial_function_total (fun y : inner_metric_space (@euclidean_inner_productP R m) =>
      (@convex_integral_geometric_measure R q k hKQ 1
        [set z | A (@euclidean_block_join R m q (y,z))] : extended_real_line R)))<=
    @convex_integral_geometric_measure R (m+q) (m+k) (leq_add (leqnn m) hKQ) 1 A.
Proof.
have hNonnegative := measure_nonnegative
  (@convex_integral_geometric_measure_is_measure R (m+q) (m+k) (leq_add (leqnn m) hKQ) 1 (lexx 1)) A.
case hMass : (@convex_integral_geometric_measure R (m+q) (m+k) (leq_add (leqnn m) hKQ) 1 A)
  => [M| |] in hNonnegative *; [|exact: leey|by []].
apply: (@nonnegative_upper_integral_increasing_bound R
  (inner_metric_space (@euclidean_inner_productP R m)) (@euclidean_lebesgue_measure R m)
  (euclidean_lebesgue_is_measure R m) (@convex_geometric_section_cutoff R m q k hKQ A)
  (fun y => (@convex_integral_geometric_measure R q k hKQ 1
    [set z | A (@euclidean_block_join R m q (y,z))] : extended_real_line R)) M).
- exact: convex_geometric_section_cutoff_nonnegative.
- exact: convex_geometric_section_cutoffs_increasing.
- exact: convex_geometric_section_cutoffs_supremum.
- move=> s.
  have hPositive : (0<(((s.+1)%:R : R)^-1))%R by rewrite invr_gt0; exact: ltr0n.
  have hBound : @convex_integral_geometric_measure R (m+q) (m+k) (leq_add (leqnn m) hKQ) 1 A<=M%:E by rewrite hMass.
  exact: (@convex_geometric_section_cutoff_integral_bound R m q k hKQ A
    (((s.+1)%:R : R)^-1)%R M _
    hPositive (metric_scale_envelope_specification _ _ _) hBound).
Qed.
