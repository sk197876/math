(** Federer (1969), 3.4.11, p. 338:
    the first coordinate of the original cusp and
    every original tangent vector is nonnegative.
    Reuse closed coordinate halfspaces and the actual
    closed dilation-containment law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra ring.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness InnerNormTopologyAdapters EuclideanCoordinateHalfspaces
  TangentConeUP TangentClosedConeContainment AnalyticCuspUP AnalyticCuspSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_cusp_first_coordinate_nonnegative]:
    the original equation x^3=y^2 forces x>=0,
    supporting the tangent formula in 3.4.11, p. 338. *)
Lemma analytic_cusp_first_coordinate_nonnegative (R:realType) (v:R_n R 2):
  @AnalyticCusp.set R v ->0<=v ord0.
Proof.
move/(@AnalyticCusp.laws R)=>hEquation.
case hSign:(0<=v ord0);first done.
exfalso.
have hNegative:v ord0<0 by rewrite ltNge hSign.
have hNonzero:v ord0!=0 by rewrite (lt_eqF hNegative).
have hSquare:0<(v ord0)^+2.
  by rewrite lt_neqAle eq_sym sqrf_eq0 hNonzero (sqr_ge0 (v ord0)).
have hCube:(v ord0)^+3=v ord0*(v ord0)^+2 by ring.
have hOther:=sqr_ge0 (v ord_max).
rewrite hCube in hEquation;nra.
Qed.

(** Source for [analytic_cusp_tangent_first_coordinate_nonnegative]:
    every actual cusp tangent has nonnegative first
    coordinate, as printed in 3.4.11, p. 338. *)
Theorem analytic_cusp_tangent_first_coordinate_nonnegative (R:realType) (v:R_n R 2):
  norm_tangent_cone (inner_norm (@euclidean_inner_productP R 2))
    (@AnalyticCusp.set R) 0 v ->0<=v ord0.
Proof.
pose X:=R_n R 2.
pose NX:=inner_norm (@euclidean_inner_productP R 2).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R 2).
pose C:set X:=[set w|0<=w ord0].
have hClosed:@closed (real_norm_metric_space hNX) C.
  have hOpen:=@euclidean_coordinate_lower_halfspace_open R 2 ord0 0.
  have hOther:=open_closedC hOpen.
  have hEqual:C=~` [set w:X|w ord0<0].
    apply:funext=>w;apply:propext;split.
    - move=>hw hNegative;have hContradiction:=le_lt_trans hw hNegative.
      by rewrite ltxx in hContradiction.
    - move=>hNot;change (is_true (0<=w ord0));rewrite leNgt;exact/negP.
  rewrite hEqual;exact:(inner_norm_closedP (@euclidean_inner_productP R 2) _).1 hOther.
apply:(@norm_tangent_closed_dilation_containment R X NX hNX (@AnalyticCusp.set R) C
  hClosed _ v)=>x hx t ht.
change (is_true (0<=(t*:x) ord0)).
rewrite ffunE.
change (is_true (0<=t*x ord0)).
exact:mulr_ge0 (ltW ht) (analytic_cusp_first_coordinate_nonnegative hx).
Qed.
