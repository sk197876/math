(** Federer (1969), 3.2.30, p. 268: the exterior-diameter
    measure of a linear image is at most the exterior operator
    norm times source measure. Apply the cost laws of 2.10.3
    at every cutoff, including the zero-norm singular case. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness OperatorNormUP OperatorNorm EuclideanLinearJacobian LipschitzUP
  ExteriorMeasure ExteriorMeasureGauge ExteriorLinearImageCost EuclideanZeroCostImage
  HausdorffLengthUP HausdorffLipschitzCost LipschitzCaratheodoryTransport MetricDiameterUP MetricDiameter
  MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_linear_positive_lipschitz_bound]:
    supporting finite-dimensional continuity of the linear map
    in Federer 3.2.30, p. 268, from its actual operator
    norm in 1.7.6, p. 33. Adding one permits a positive
    cutoff factor even when the map is zero. *)
Lemma euclidean_linear_positive_lipschitz_bound (R:realType) s n
    (L:Hom (R_n R s) (R_n R n)):
  exists M,(0<M)%R /\ @is_metric_lipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R s))
    (inner_metric_space (@euclidean_inner_productP R n)) setT L M.
Proof.
pose C:=linear_operator_norm (@euclidean_inner_productP R s) (@euclidean_inner_productP R n)
  (@coordinate_basisP R s) (hom_as_linear L).
have hC:(0<=C)%R:=linear_operator_norm_nonnegative _ _ _ _.
have hGe:(1<=C+1)%R by rewrite lerDr; exact hC.
have hM:(0<C+1)%R:=lt_le_trans ltr01 hGe.
exists (C+1)%R; split; first exact hM.
split; first exact:ltW hM.
move=>x y _ _; rewrite !inner_metric_distanceE.
change (is_true ((inner_norm (@euclidean_inner_productP R n)
  (hom_as_linear L x-hom_as_linear L y)<=(C+1)*inner_norm (@euclidean_inner_productP R s) (x-y))%R)).
rewrite -linearB.
apply:le_trans (operator_norm_vector_bound
  (linear_operator_normP (@euclidean_inner_productP R s) (@euclidean_inner_productP R n)
    (@coordinate_basisP R s) (hom_as_linear L)) (x-y)) _.
have hCo:(C<=C+1)%R by rewrite lerDl ler01.
exact (ler_wpM2r (inner_norm_nonnegative (@euclidean_inner_productP R s) (x-y)) hCo).
Qed.

(** Source for [linear_exterior_measure_image_bound]: the first
    inequality of Federer 3.2.30, p. 268. All arbitrary
    sets and singular maps are retained; no finite mass or
    measurability premise is added. The supporting statement
    also permits degree zero under the existing cost convention. *)
Theorem linear_exterior_measure_image_bound (R:realType) s n k
    (L:Hom (R_n R s) (R_n R n)) (A:set (R_n R s)):
  (@exterior_diameter_measure R n k (L @` A)<=
    (euclidean_linear_jacobian k L)%:E*@exterior_diameter_measure R s k A).
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R s).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose J:=euclidean_linear_jacobian k L.
have hJ:(0<=J)%R:=euclidean_linear_jacobian_nonnegative k L.
have [M [hM hBound]]:=euclidean_linear_positive_lipschitz_bound L.
case:(eqVneq J (0%R:R))=>hZero.
- have hCost (B:set X):B!=set0 ->exterior_diameter_cost k (L @` B)=0.
    move=>hB; have hh:=@exterior_linear_cost_bound R s n k L B.
    rewrite /J in hZero; rewrite hZero mul0e in hh.
    by apply/eqP; rewrite eq_le hh exterior_diameter_cost_nonnegative.
  have hImage:=@euclidean_zero_cost_lipschitz_image R s Y L M
    (@exterior_diameter_cost R n k) (@exterior_diameter_measure R n k) hBound
    (exterior_diameter_measure_specification R n k)
    (fun B _=>exterior_diameter_cost_nonnegative k B) hCost A.
  rewrite /J in hZero.
  by rewrite hImage hZero mul0e.
- have hPos:(0<J)%R by rewrite lt_neqAle eq_sym hZero hJ.
  have hImage (j:@nonempty_metric_sets R X):(L @` val j)!=set0.
    have [x hx]:=set_valP j; exists (L x); by exists x.
  pose v (j:@nonempty_metric_sets R X):@nonempty_metric_sets R Y:=
    @exist _ (fun B=>B \in [set B|B!=set0]) (L @` val j) (mem_set (hImage j)).
  exact (@lipschitz_caratheodory_transport R X Y (@nonempty_metric_sets R X) (@nonempty_metric_sets R Y)
    (fun j=>val j) (fun j=>val j) (fun j=>exterior_diameter_cost k (val j))
    (fun j=>exterior_diameter_cost k (val j)) L v
    (@exterior_diameter_measure R s k) (@exterior_diameter_measure R n k) M J
    (exterior_diameter_measure_specification R s k) (exterior_diameter_measure_specification R n k)
    (fun j=>exterior_diameter_cost_nonnegative k (val j)) hM hPos
    (fun j x hx=>ex_intro2 _ _ x hx (erefl _))
    (fun j=>extended_metric_diameter_lipschitz hBound (val j))
    (fun j=>@exterior_linear_cost_bound R s n k L (val j)) A).
Qed.
