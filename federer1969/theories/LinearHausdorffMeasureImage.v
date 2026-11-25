(** Federer (1969), 3.2.30, p. 268: combine the actual
    exterior image bound with 2.10.39 to bound Hausdorff
    measure, for every positive integer degree. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLinearJacobian LinearExteriorMeasureImage ExteriorMeasure EuclideanExteriorLebesgue
  SphericalExteriorTheorem HausdorffMeasure HausdorffSphericalComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [linear_hausdorff_measure_exterior_bound]: the
    second inequality of Federer 3.2.30, p. 268. Write
    n^(k/2) as sqrt(n)^k, exactly as in the proved 2.10.39
    interface. Every arbitrary source set is retained, including
    infinite mass, singular maps, zero-dimensional ambient spaces
    and positive degrees above either ambient dimension. *)
Theorem linear_hausdorff_measure_exterior_bound (R:realType) s n k
    (L:Hom (R_n R s) (R_n R n)) (A:set (R_n R s)):
  (0<k)%N ->
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) k (L @` A)<=
    ((Num.sqrt n%:R)^+k*2^+k.-1*euclidean_linear_jacobian k L)%:E*
      @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R s)) k A).
Proof.
move=>hk.
pose C:R:=((Num.sqrt n%:R)^+k*2^+k.-1)%R.
have hC:(0<=C)%R:=mulr_ge0 (exprn_ge0 k (sqrtr_ge0 _)) (exprn_ge0 k.-1 (ler0n R 2)).
have hJ:(0<=euclidean_linear_jacobian k L)%R:=euclidean_linear_jacobian_nonnegative k L.
have hCE:(0<=C%:E)%E by rewrite lee_fin.
have hJE:(0<=(euclidean_linear_jacobian k L)%:E)%E by rewrite lee_fin.
have hT:=@linear_exterior_measure_image_bound R s n k L A.
have hSource:=@exterior_measure_hausdorff_bound R s k A.
have hTH:=le_trans hT (lee_wpmul2l hJE hSource).
have hScaled:=lee_wpmul2l hCE hTH.
have hS:=@spherical_exterior_measure_bound R n k (L @` A) hk.
have hH:=@hausdorff_measure_le_spherical_measure R
  (inner_metric_space (@euclidean_inner_productP R n)) k (L @` A).
have hResult:=le_trans hH (le_trans hS hScaled).
by rewrite muleA -EFinM in hResult.
Qed.

(** Source for [federer_3_2_30]: both displayed inequalities
    of Federer 3.2.30, p. 268, proved from actual
    endpoint costs, the covering construction and 2.10.39.
    Euclidean spaces are represented by their coordinate models,
    as in the preceding public measure interfaces. *)
Theorem federer_3_2_30 (R:realType) s n k
    (L:Hom (R_n R s) (R_n R n)) (A:set (R_n R s)):
  (0<k)%N ->
  (@exterior_diameter_measure R n k (L @` A)<=
    (euclidean_linear_jacobian k L)%:E*@exterior_diameter_measure R s k A) /\
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) k (L @` A)<=
    ((Num.sqrt n%:R)^+k*2^+k.-1*euclidean_linear_jacobian k L)%:E*
      @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R s)) k A).
Proof.
move=>hk; split; first exact:linear_exterior_measure_image_bound.
exact (@linear_hausdorff_measure_exterior_bound R s n k L A hk).
Qed.
