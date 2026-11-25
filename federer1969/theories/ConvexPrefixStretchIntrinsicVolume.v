(** Iterated actual coordinate stretching for the section
    comparison in Federer (1969), 3.2.45,
    pp. 279–280. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric InnerConvex
  EuclideanLinearMaps EuclideanAffineImageGeometry ScalarConvexLength IntegralGeometricGauge
  EuclideanCoordinateStretch EuclideanPrefixStretch.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_prefix_stretch_intrinsic_volume]: supporting
    separately proved coefficient bound in the anisotropic
    argument for Federer 3.2.45,
    pp. 279–280. Stretching the
    first m actual coordinates by t>=1
    increases every intrinsic coefficient by at
    most t^m. Iterate the proved
    one-coordinate estimate and the exact prescribed
    diagonal-map composition law. The empty block
    is the identity. Thin bodies and
    every natural intrinsic degree, including zero,
    are retained. No coefficientwise inference from
    a polynomial inequality is made. *)
Theorem convex_prefix_stretch_intrinsic_volume (R : realType) n k (hKN : (k<=n)%N)
    m (hMN : (m<=n)%N)
    (K : set (inner_metric_space (@euclidean_inner_productP R n))) (t : R) :
  K !=set0 -> compact K -> is_inner_convex K -> (1<=t)%R ->
  @integral_geometric_gauge R n k hKN 1
    ((@euclidean_diagonal_map R n (fun j => if (j<m)%N then t else 1%R)) @` K) <=
    (t^+m)%R%:E*@integral_geometric_gauge R n k hKN 1 K.
Proof.
move=> hNonempty hCompact hConvex hT.
pose X := inner_metric_space (@euclidean_inner_productP R n).
elim: m hMN=> [hMN|m hInduction hMN].
- have hImage : (@euclidean_diagonal_map R n (fun j => if (j<0)%N then t else 1%R)) @` K=K.
    apply/seteqP; split.
    + move=> x [y hy <-]; by rewrite euclidean_prefix_stretch_zero.
    + move=> x hx; exists x=> //; exact: euclidean_prefix_stretch_zero.
  by rewrite hImage expr0 mul1e.
- pose D := @euclidean_diagonal_map R n (fun j => if (j<m)%N then t else 1%R).
  pose i : 'I_n := Ordinal hMN.
  have hPrevious := hInduction (leq_trans (leqnSn m) hMN).
  have hDNonempty : D @` K !=set0.
    have [x hx] := hNonempty; exists (D x); by exists x.
  have hDCompact : @compact [the topologicalType of X] (D @` K).
    have h := @euclidean_affine_hom_compact_image R n n (hom_of_linear D) (0%R:X) K hCompact.
    have hFunction : (fun x : X => 0+hom_of_linear D x)%R=(D : X -> X).
      apply: funext=> x; by rewrite hom_of_linearE add0r.
    by rewrite hFunction in h.
  have hDConvex : is_inner_convex (D @` K) := linear_image_inner_convex hConvex.
  have hStep := @convex_coordinate_stretch_intrinsic_volume R n k hKN (D @` K)
    i t hDNonempty hDCompact hDConvex hT.
  have hImage : (@euclidean_diagonal_map R n (fun j => if j==i then t else 1%R)) @` (D @` K)=
      (@euclidean_diagonal_map R n (fun j => if (j<m.+1)%N then t else 1%R)) @` K.
    rewrite image_comp; congr (_ @` K); apply: funext=> x.
    exact: esym (@euclidean_prefix_stretch_successor R n m t hMN x).
  rewrite hImage in hStep.
  have hScaled := lee_wpmul2l (lee_tofin (le_trans (@ler01 R) hT)) hPrevious.
  have hPower : (t%:E*((t^+m)%R%:E*@integral_geometric_gauge R n k hKN 1 K))=
      ((t^+m.+1)%R%:E*@integral_geometric_gauge R n k hKN 1 K).
    rewrite exprS EFinM muleA; reflexivity.
  rewrite hPower in hScaled.
  exact: le_trans hStep hScaled.
Qed.
