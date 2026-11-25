(** Federer (1969), 4.1.12, p. 368: a
    normal one-current on the line cannot be
    supported at a point. Its represented boundary
    is point-supported and has total zero; the
    preceding compact top-degree uniqueness then applies. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentBoundary CurrentBoundarySupport
  NormalCurrentsUP CurrentCompactBoundarySmooth CurrentCompactBoundaryTotal CurrentRepresentedPointTotal
  CurrentCompactCurrentArithmetic CurrentCompactTopUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_normal_point_support_zero]:
    an original normal one-current on R supported
    in one point is zero. This proves a
    supporting case of the obstruction explicitly anticipated
    in Federer 4.1.12, p. 368, using only
    the preceding representation and uniqueness laws.
    Empty support and arbitrary open domains are included. *)
Theorem current_normal_point_support_zero (R:realType) (h2:(1+1:R)!=0)
    (U:set (R_n R 1%N))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R 1%N)) U x)
    (T:@current_space R h2 1%N U hU 1%N) x:
  @is_normal_current R h2 1%N U hU 1%N T->
  @current_support R h2 1%N U hU 1%N T `<=` [set x]->T=0.
Proof.
move=>hNormal hPoint.
pose B:=@current_boundary R h2 1%N 0%N U hU T.
pose hCompactB:=@current_compact_boundary_compact R h2 1%N 0%N U hU T hNormal.2.
have hPointB:@current_support R h2 1%N U hU 0%N B `<=` [set x].
  move=>y hy;exact:(hPoint y (@current_boundary_support_subset R h2 1%N 0%N U hU T y hy)).
have hBZero:B=0.
  apply:(@current_represented_point_total_zero R h2 1%N U hU B hNormal.1.2 hCompactB x hPointB).
  exact:(@current_compact_boundary_total_zero R h2 1%N U hU T hNormal.2).
apply:(@current_compact_top_boundary_unique R h2 1%N 0%N U hU T 0 hNormal.2
  (@current_compact_zero_support R h2 1%N 1%N U hU) (erefl 1%N)).
rewrite linear0;exact:hBZero.
Qed.
