(** Federer (1969), 3.2.36, p. 273: express the
    proved intrinsic-volume convolution by finite generating polynomials. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP
  IntegralGeometricGauge ConvexIntrinsicFinitePart SteinerTubePolynomial EuclideanCartesianMap
  EuclideanCartesianConvexGeometry BoundedConvexCartesianIntrinsicVolumes FiniteConvolutionPolynomialProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [convex_intrinsic_generating_polynomial]: the finite
    polynomial of actual intrinsic-volume coefficients used to identify
    the box edge functions in Federer 3.2.36, p. 273.
    Scalar parts are used below only after their actual nonnegative
    finiteness is proved for the original bounded convex source. *)
Definition convex_intrinsic_generating_polynomial (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) (t:R):R:=
  \sum_(i:'I_n.+1) fine (@integral_geometric_gauge R n i (steiner_dimension_guard i) 1 S)*t^+i.

(** Source for [convex_cartesian_intrinsic_generating_polynomial]: the
    polynomial form of the complete convolution in Federer 3.2.36,
    p. 273, supporting its elementary symmetric-function consequence.
    Every actual coefficient is first known finite; exact embedded
    scalar comparison then transports the already proved original-set
    convolution. No additional geometry, integration or coefficient
    hypothesis is added. All natural coordinate blocks and real
    polynomial parameters, including zero and negative ones, remain. *)
Theorem convex_cartesian_intrinsic_generating_polynomial (R:realType) m n
    (A:set (inner_metric_space (@euclidean_inner_productP R m)))
    (B:set (inner_metric_space (@euclidean_inner_productP R n))):
  A!=set0 ->B!=set0 ->is_inner_convex A ->is_inner_convex B ->
  metric_set_bounded A ->metric_set_bounded B ->forall t:R,
    convex_intrinsic_generating_polynomial (euclidean_cartesian_set A B) t=
    convex_intrinsic_generating_polynomial A t*convex_intrinsic_generating_polynomial B t.
Proof.
move=>hAN hBN hA hB hABound hBBound t.
have hPN:=euclidean_cartesian_nonempty hAN hBN.
have hPC:=euclidean_cartesian_convex hA hB.
have hPB:=euclidean_nonempty_cartesian_bounded hAN hBN hABound hBBound.
have hG (i:'I_m.+1):@integral_geometric_gauge R m i (steiner_dimension_guard i) 1 A=
    (fine (@integral_geometric_gauge R m i (steiner_dimension_guard i) 1 A))%:E.
  exact:convex_intrinsic_finite_part_value hAN hA hABound.
have hH (j:'I_n.+1):@integral_geometric_gauge R n j (steiner_dimension_guard j) 1 B=
    (fine (@integral_geometric_gauge R n j (steiner_dimension_guard j) 1 B))%:E.
  exact:convex_intrinsic_finite_part_value hBN hB hBBound.
have hCoeff (l:'I_(m+n).+1):
    fine (@integral_geometric_gauge R (m+n) l (steiner_dimension_guard l) 1 (euclidean_cartesian_set A B))=
    \sum_(i:'I_m.+1) \sum_(j:'I_n.+1|(i+j==l)%N)
      fine (@integral_geometric_gauge R m i (steiner_dimension_guard i) 1 A)*
      fine (@integral_geometric_gauge R n j (steiner_dimension_guard j) 1 B).
  apply:EFin_inj.
  rewrite -(@convex_intrinsic_finite_part_value R (m+n) l (steiner_dimension_guard l)
    (euclidean_cartesian_set A B) hPN hPC hPB)
    (@bounded_convex_cartesian_intrinsic_volumes R m n A B hAN hBN hA hB hABound hBBound l) -sumEFin.
  apply:eq_bigr=>i _; rewrite -sumEFin; apply:eq_bigr=>j _.
  by rewrite hG hH -EFinM.
rewrite /convex_intrinsic_generating_polynomial finite_convolution_polynomial_product.
apply:eq_bigr=>l _; by rewrite hCoeff.
Qed.
