(** Federer (1969), 2.10.47, pp. 204–205: choose a positive root cube and
    apply the proved pruning theorem. This removes the temporary root-cube
    restriction; nullity of coordinate sections is retained for the
    ambient-dimension induction. Source context: CompactPositiveUnitCube.v
    and DyadicNullSectionsCompactSubset.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueHaar
  CompactPositiveUnitCube DyadicNullSectionsCompactSubset MetricRealPowerMeasureUP
  MetricRealPowerMeasureLaws MeasureUP MeasureBasic MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_null_sections_finite_positive_subset]:
    the root-cube choice and main construction in
    2.10.47, pp. 204–205, before removing section
    nullity by induction. No boundedness or cube premise
    is added to compactness of the original source. *)
Theorem compact_null_sections_finite_positive_subset (R : realType) n c p
    (mu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_metric_real_power_measure c p mu -> (0<n)%N -> (0<c)%R -> (0<p)%R -> compact A ->
  (forall (l : 'I_n) (t : R), mu (A `&` [set x | x l=t])=0) -> 0<mu A ->
  exists B, [/\ compact B, B `<=` A, 0<mu B & mu B< +oo].
Proof.
move=> hmu hn hc hp hA hlevels hpos.
pose X := inner_metric_space (@euclidean_inner_productP R n).
have hm := metric_real_power_measure_law (ltW hc) hmu.
have [a ha] := compact_positive_unit_cube hm hA hpos.
pose C := [set x : X | forall l, (a l<=x l<=a l+1)%R].
have hC : compact C := @euclidean_closed_box_compact R n a (fun l=>(a l+1)%R).
have hAC : compact (A `&` C) := compact_closedI hA (compact_closed (@metric_hausdorff R X) hC).
have hr x (hx : (A `&` C) x) : forall l, (a l<=x l<=a l+1)%R := hx.2.
have hnull (l : 'I_n) (t : R) : mu ((A `&` C) `&` [set x | x l=t])=0.
  apply: (@measure_null_subset R X mu hm _ (A `&` [set x | x l=t])); last exact: hlevels.
  by move=> x [[hx _] ht]; split.
have [B [hBc hB hBp hBf]] := @dyadic_null_sections_compact_subset R n a c p mu (A `&` C)
  hmu hn hc hp hAC hr hnull ha.
exists B; split=> //; by move=> x hx; have [h _] := hB x hx.
Qed.
