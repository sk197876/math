(** Original unrestricted bounded convex section comparison
    in Federer (1969), 3.2.45, p. 279. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP
  EuclideanBlockCoordinates InnerConvexNeighbourhoods MetricBoundedClosureLaws IntegralGeometricGauge
  CompactConvexBlockSections CartesianSectionDiameter BoundedConvexIntrinsicSubsetOrder ConvexProjectedClosureVolume
  CompactConvexIntrinsicSectionComparison BoundedConvexIntrinsicSectionIntegrability EuclideanLebesgueDimensions
  PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  MeasureIntegralBounds MeasureIntegralUniqueness MeasureUpperIntegralMonotone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [bounded_convex_intrinsic_section_comparison]: direct
    original convex section inequality in Federer 3.2.45,
    p. 279. Every original nonempty bounded convex
    K is retained. Its actual section function has
    the proved finite ordinary integral from Fubini
    on original open tubes. Inclusion in the compact
    source closure, original convex intrinsic monotonicity
    and the proved compact section theorem bound that
    integral. The exact original gauge closure law
    restores the right member. No pointwise equality
    of section closures, Borel premise, source interior,
    positive mass or nonempty-fibre condition is added.
    Both degree endpoints and either empty block remain. *)
Theorem bounded_convex_intrinsic_section_comparison (R : realType) m q k (hKQ : (k<=q)%N)
    (K : set (inner_metric_space (@euclidean_inner_productP R (m+q)))) :
  K !=set0 -> is_inner_convex K -> metric_set_bounded K ->
  exists a : R,
    is_measure_integral (@euclidean_lebesgue_measure R m)
      (partial_function_total (fun y : inner_metric_space (@euclidean_inner_productP R m) =>
        @integral_geometric_gauge R q k hKQ 1 [set z | K (@euclidean_block_join R m q (y,z))])) a%:E /\
    a%:E<= @integral_geometric_gauge R (m+q) (m+k) (leq_add (leqnn m) hKQ) 1 K.
Proof.
move=> hNonempty hConvex hBound.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose Z := inner_metric_space (@euclidean_inner_productP R (m+q)).
pose mu := @euclidean_lebesgue_measure R m.
pose hm := euclidean_lebesgue_is_measure R m.
pose F := fun y : X => @integral_geometric_gauge R q k hKQ 1
  [set z | K (@euclidean_block_join R m q (y,z))].
pose H := fun y : X => @integral_geometric_gauge R q k hKQ 1
  [set z | closure K (@euclidean_block_join R m q (y,z))].
have [a hIntegralA] := @bounded_convex_intrinsic_section_integrability R m q k hKQ K
  hNonempty hConvex hBound.
have hClosureNonempty : closure K !=set0.
  have [x hx] := hNonempty; exists x; exact: subset_closure hx.
have hClosureCompact := euclidean_bounded_closure_compact hBound.
have hClosureBound := metric_bounded_closure hBound.
have hClosureConvex := @inner_convex_closure R (R_n R (m+q)) (@euclidean_inner_product R (m+q))
  (@euclidean_inner_productP R (m+q)) K hConvex.
have [b [hIntegralB hBoundB]] := @compact_convex_intrinsic_section_comparison R m q k hKQ
  (closure K) hClosureNonempty hClosureCompact hClosureConvex.
have hOrder y : F y<=H y.
  apply: (@bounded_convex_intrinsic_subset_order R q k hKQ
    [set z | K (@euclidean_block_join R m q (y,z))]
    [set z | closure K (@euclidean_block_join R m q (y,z))]
    (@euclidean_block_section_inner_convex R m q K y hConvex)
    (@euclidean_block_section_inner_convex R m q (closure K) y hClosureConvex)
    (@euclidean_bounded_block_section R m q K y hBound)
    (@euclidean_bounded_block_section R m q (closure K) y hClosureBound))=> z hz.
  have hOriginal : K (@euclidean_block_join R m q (y,z)) := hz.
  exact: (@subset_closure [the topologicalType of Z] K _ hOriginal).
have hAlmost : measure_almost_everywhere mu
    (partial_extended_le_locus (partial_function_total F) (partial_function_total H)).
  apply: (measure_almost_everywhere_mono hm _ (measure_almost_everywhere_true hm))=> y _.
  exists (F y),(H y); split=> //; split=> //; exact: hOrder.
have hUpper := @measure_upper_integral_monotone R X mu hm
  (partial_function_total F) (partial_function_total H) hAlmost.
have hValueA := @measure_upper_integral_unique R X mu (partial_function_total F) _ a%:E
  (measure_upper_integral_specification mu (partial_function_total F)) hIntegralA.2.1.
have hValueB := @measure_upper_integral_unique R X mu (partial_function_total H) _ b%:E
  (measure_upper_integral_specification mu (partial_function_total H)) hIntegralB.2.1.
rewrite hValueA hValueB in hUpper.
rewrite (@convex_integral_geometric_gauge_closure R (m+q) (m+k) (leq_add (leqnn m) hKQ) 1
  K hNonempty hConvex hBound) in hBoundB.
exists a; split; first exact hIntegralA.
exact: le_trans hUpper hBoundB.
Qed.
