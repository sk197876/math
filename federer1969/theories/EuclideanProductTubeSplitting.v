(** Federer (1969), 3.2.36, p. 273: split the whole actual
    product tube into zero and positive first-distance pieces. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates
  EuclideanCartesianMap CompactHausdorffMetric CompactSetDistanceProfile EuclideanProductDistanceBounds
  EuclideanFirstCylinderDistance EuclideanProductTubeZeroSlice EuclideanLebesgueDimensions EuclideanLebesgueBoxes
  MetricSetDistanceUP MetricSetDistanceBasic MetricSetDistanceContinuity RealMetricBackground
  TopologicalBorel BorelRegularMeasureUP MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_product_tube_volume_splitting]: the first
    equality of Federer 3.2.36, p. 273, with its actual two
    disjoint volume terms. The first-distance zero locus is closed;
    its measurable splitting law applies to the entire product tube.
    Nonnegativity and the proved first-distance bound identify the
    remainder with the printed positive strip. No convexity or
    full-dimensionality is needed for this geometric splitting. *)
Theorem euclidean_product_tube_volume_splitting (R:realType) m n
    (A:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R m)))
    (B:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n)))
    (d:inner_metric_space (@euclidean_inner_productP R (m+n))->R) (r:R):
  @is_metric_set_distance R (inner_metric_space (@euclidean_inner_productP R (m+n)))
    (euclidean_cartesian_set (val A) (val B)) d ->0<r ->
  let f:=fun z:inner_metric_space (@euclidean_inner_productP R (m+n))=>
    compact_set_distance_profile A (euclidean_block_split z).1 in
  @euclidean_lebesgue_measure R (m+n) [set z|d z<r]=
    (@euclidean_lebesgue_measure R m (val A)*
      @euclidean_lebesgue_measure R n [set y|(compact_set_distance_profile B y<r)%R]+
      @euclidean_lebesgue_measure R (m+n) ([set z|(0<f z<r)%R] `&` [set z|(d z<r)%R]))%E.
Proof.
move=>hD hr f.
pose Z:=inner_metric_space (@euclidean_inner_productP R (m+n)).
pose C:set Z:=[set z|f z=0].
pose T:set Z:=[set z|d z<r].
have [_ [_ hCylinder]]:=@euclidean_first_cylinder_distance R m n A.
have hClosed:closed C.
  change (closed ((f:Z->real_line_metric R) @^-1` [set (0:R)])).
  apply:preimage_closed.
  - move=>z _; exact:(@metric_set_distance_continuous R Z _ f hCylinder z).
  - apply:accessible_closed_set1; apply:hausdorff_accessible; exact:metric_hausdorff.
have hMeasurable:measure_measurable (@euclidean_lebesgue_measure R (m+n)) C.
  apply:euclidean_borel_measurable; exact:closed_borel_set hClosed.
have hZero:T `&` C=[set z:Z|f z=0 /\d z<r].
  apply/seteqP; split=>z [hz ht]; by split.
have hPositive:T `\` C=[set z|0<f z<r] `&` T.
  apply/seteqP; split=>z.
  - move=>[hz hn]; split=>//; apply/andP; split.
    + rewrite lt_neqAle eq_sym (metric_set_distance_nonnegative hCylinder z) andbT.
      apply/eqP=>he; exact:hn he.
    + exact:le_lt_trans (@euclidean_first_distance_le_product R m n A (val B) d hD z) hz.
  - move=>[/andP[hz0 hzr] hz]; split=>//.
    move=>he; change (f z=0) in he; by rewrite he ltxx in hz0.
rewrite (hMeasurable T) hZero hPositive (@euclidean_product_tube_zero_slice R m n A B d r hD hr).
by [].
Qed.
