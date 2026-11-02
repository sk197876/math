(** Federer (1969), 3.2.33, p. 270: the printed map
    satisfies the finite Lipschitz hypothesis of 3.2.32 on W. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness RealNormUP RealMetricBackground RealOpenIntervals LipschitzUP
  EuclideanCoordinateTopology EuclideanCoordinateMetric EuclideanOpenUnitCube ScalarCylinderMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_cylinder_lipschitz]: the smooth example
    retains the Lipschitz hypothesis of Federer 3.2.32,
    supporting 3.2.33, p. 270. Every image-coordinate
    difference is bounded by the source distance. Finite
    coordinate synthesis gives a finite bound mu+1 on W;
    optimality of that bound is not required or asserted. *)
Theorem scalar_cylinder_lipschitz (R:realType) mu k (g:R->R)
    (F:R_n R ((mu+1)+k)->R_n R (mu+1)):
  is_scalar_cylinder_map g F ->
  @is_metric_lipschitz_bound R (real_line_metric R) (real_line_metric R) (real_open_interval 0 1) g 1 ->
  @is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R ((mu+1)+k)))
    (inner_metric_space (@euclidean_inner_productP R (mu+1)))
    (@euclidean_open_unit_cube R ((mu+1)+k)) F.
Proof.
move=>hF hG.
exists (mu+1)%:R; split; first by rewrite ltr0n addn1.
split; first exact:ler0n.
move=>x y hx hy; rewrite !inner_metric_distanceE.
pose NX:=inner_norm (@euclidean_inner_productP R ((mu+1)+k)).
pose NY:=inner_norm (@euclidean_inner_productP R (mu+1)).
have hCoord i:`|(F x-F y) i|<=NX (x-y).
  rewrite -(splitK i); case:(split i)=>j.
  - rewrite !ffunE !(scalar_cylinder_first_coordinates hF).
    have h:=euclidean_coordinate_norm_bound (lshift k (lshift 1 j)) (x-y).
    rewrite !ffunE in h; exact h.
  - rewrite (ord1 j) !ffunE !(scalar_cylinder_last_coordinate hF).
    have hxT:real_open_interval 0 1 (x (lshift k (rshift mu ord0))).
      by have /andP [h0 h1]:=hx (lshift k (rshift mu ord0)); split.
    have hyT:real_open_interval 0 1 (y (lshift k (rshift mu ord0))).
      by have /andP [h0 h1]:=hy (lshift k (rshift mu ord0)); split.
    have h:=hG.2 _ _ hxT hyT; rewrite !real_line_metric_distanceE mul1r in h.
    have hSource:=euclidean_coordinate_norm_bound (lshift k (rshift mu ord0)) (x-y).
    rewrite !ffunE in hSource.
    exact:(le_trans h hSource).
have hSum:NY (F x-F y)<=\sum_(i:'I_(mu+1)) NX (x-y).
  rewrite -{1}(euclidean_coordinate_expansion (F x-F y)).
  apply:le_trans (real_seminorm_sum (inner_norm_real_norm (@euclidean_inner_productP R (mu+1))).1 _) _.
  apply:ler_sum=>i _; rewrite /NY inner_normZ euclidean_coordinate_unit_norm mulr1.
  exact:hCoord.
by rewrite sumr_const card_ord -mulr_natl in hSum.
Qed.
