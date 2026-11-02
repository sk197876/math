(** Federer (1969), 3.2.36, p. 273: the coordinate
    box's actual intrinsic volumes are the elementary symmetric edge coefficients. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  CoordinateEdgeBoxGeometry CoordinateEdgeBoxFactorization CoordinateEdgeBoxBase
  ConvexIntrinsicGeneratingPolynomial ElementarySymmetricCoefficientsUP IntegralGeometricGauge
  ConvexIntrinsicFinitePart SteinerTubePolynomial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coordinate_edge_box_intrinsic_polynomial]: the
    complete rectangular-edge consequence of Federer 3.2.36,
    p. 273, first in the standard coordinates. The actual
    original Cartesian convolution, the independently proved line
    coefficients and the exact carrier decomposition give the product
    of 1+c_i t by dimension induction. Every nonnegative edge
    vector, including zero widths and the empty family, is retained.
    The identity holds for every real polynomial parameter. *)
Theorem coordinate_edge_box_intrinsic_polynomial (R:realType):
  forall n (c:'I_n->R),(forall i,0<=c i) ->forall t:R,
    convex_intrinsic_generating_polynomial (coordinate_edge_box c) t=
      \prod_(i:'I_n) (1+c i*t).
Proof.
elim=>[c hc t|n hIH c hc t].
- by rewrite coordinate_edge_box_zero_polynomial big_ord0.
- pose first:=fun _:'I_1=>c ord0.
  pose tail:=fun i:'I_n=>c (rshift 1 i).
  have hFirst:forall i,0<=first i by move=>i; exact:hc.
  have hTail:forall i,0<=tail i by move=>i; exact:hc.
  rewrite coordinate_edge_box_factorization.
  rewrite (@convex_cartesian_intrinsic_generating_polynomial R 1 n
    (coordinate_edge_box first) (coordinate_edge_box tail)
    (coordinate_edge_box_nonempty hFirst) (coordinate_edge_box_nonempty hTail)
    (@coordinate_edge_box_convex R 1 first) (@coordinate_edge_box_convex R n tail)
    (coordinate_edge_box_bounded hFirst) (coordinate_edge_box_bounded hTail) t).
  rewrite (coordinate_edge_box_line_polynomial t hFirst) (hIH tail hTail t).
  symmetry; exact:coordinate_edge_linear_factor_product.
Qed.

(** Source for [coordinate_edge_box_elementary_symmetric_coefficients]:
    the m-th elementary symmetric edge functions asserted in Federer
    3.2.36, p. 273, using their independent product-polynomial
    laws. The actual intrinsic-volume coefficients satisfy these laws;
    uniqueness was proved before this geometry theorem. Apply erratum
    p. 5, book p. 273 line 18: m-th. *)
Theorem coordinate_edge_box_elementary_symmetric_coefficients (R:realType) n (c:'I_n->R):
  (forall i,0<=c i) ->
  is_elementary_symmetric_coefficients c (fun j:'I_n.+1=>
    fine (@integral_geometric_gauge R n j (steiner_dimension_guard j) 1 (coordinate_edge_box c))).
Proof.
move=>hc t; symmetry; exact:coordinate_edge_box_intrinsic_polynomial hc t.
Qed.

(** Source for [coordinate_edge_box_elementary_symmetric_existence]:
    existence with actual finite intrinsic-volume values for all the
    elementary symmetric edge coefficients in Federer 3.2.36,
    p. 273. The independent coefficient laws and actual finite
    gauge identities are proved together; no global chosen coefficient
    family, positive-width convention or infinite-value default is used. *)
Corollary coordinate_edge_box_elementary_symmetric_existence (R:realType) n (c:'I_n->R):
  (forall i,0<=c i) ->exists e:'I_n.+1->R,
    is_elementary_symmetric_coefficients c e /\forall j:'I_n.+1,
      @integral_geometric_gauge R n j (steiner_dimension_guard j) 1 (coordinate_edge_box c)=(e j)%:E.
Proof.
move=>hc; exists (fun j:'I_n.+1=>fine (@integral_geometric_gauge R n j (steiner_dimension_guard j) 1
  (coordinate_edge_box c))).
split; first exact:coordinate_edge_box_elementary_symmetric_coefficients hc.
move=>j; exact:convex_intrinsic_finite_part_value (coordinate_edge_box_nonempty hc)
  (@coordinate_edge_box_convex R n c) (coordinate_edge_box_bounded hc).
Qed.
