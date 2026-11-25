(** Federer (1969), 3.2.36, p. 273: the zero first-distance
    slice has the actual product of the two displayed factor volumes. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates
  EuclideanCartesianMap CompactHausdorffMetric CompactSetDistanceProfile EuclideanProductTubeFibres
  EuclideanBlockRectangleMass EuclideanLebesgueDimensions EuclideanLebesgueBoxes EuclideanBoundedRectifiability
  MetricSetDistanceUP TopologicalBorel BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_product_tube_zero_slice]: the term
    L^mu(P) L^nu{z:dist(z,Q)<r} in Federer 3.2.36, p. 273.
    The exact product-distance fibre at zero, compact-factor zero-set
    laws and the measurable rectangle formula prove the actual mass.
    Lower-dimensional compact factors and either empty coordinate block
    remain, with no interior or positive-volume premise. *)
Theorem euclidean_product_tube_zero_slice (R:realType) m n
    (A:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R m)))
    (B:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n)))
    (d:inner_metric_space (@euclidean_inner_productP R (m+n))->R) (r:R):
  @is_metric_set_distance R (inner_metric_space (@euclidean_inner_productP R (m+n)))
    (euclidean_cartesian_set (val A) (val B)) d ->0<r ->
  @euclidean_lebesgue_measure R (m+n)
    [set z:inner_metric_space (@euclidean_inner_productP R (m+n))|
      compact_set_distance_profile A (euclidean_block_split z).1=0 /\d z<r]=
    (@euclidean_lebesgue_measure R m (val A)*
      @euclidean_lebesgue_measure R n [set y|(compact_set_distance_profile B y<r)%R])%E.
Proof.
move=>hD hr.
have hF:=@euclidean_product_tube_first_distance_fibre R m n A B d 0 r hD (lexx 0) hr.
have hZero:[set x|compact_set_distance_profile A x=0]=val A.
  apply/seteqP; split=>x hx.
  - exact:(compact_set_distance_profile_zero A x).1 hx.
  - exact:(compact_set_distance_profile_zero A x).2 hx.
rewrite expr0n /= subr0 sqrtr_sqr (ger0_norm (ltW hr)) hZero in hF.
rewrite hF /euclidean_cartesian_set.
apply:euclidean_block_rectangle_mass.
- apply:euclidean_borel_measurable; apply:closed_borel_set.
  exact:compact_closed (@metric_hausdorff R (inner_metric_space (@euclidean_inner_productP R m))) (set_valP A).1.
- apply:euclidean_borel_measurable.
  exact:(@compact_distance_tube_rectifiable R n B r hr).2.1.
Qed.
