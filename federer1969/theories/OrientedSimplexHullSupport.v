(** Earlier source scope: Federer (1969), 4.1.22, p. 379,
    uses the actual simplex currents of 4.1.11, pp. 365–366.
    Their fixed-index normality gives the original inclusion
    diagram in 4.1.24, p. 381. The retained source comments
    also identify their later use in 4.1.32. These prerequisites use the original public simplex operations. *)
(** Federer (1969), 4.1.32, p. 392: the
    support of the original simplex lies in the
    convex hull of its vertices. This is the
    preceding point-join support property applied along
    the original recursion of 4.1.11. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm InnerConvex HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct ConvexHull CurrentSpaces CurrentSupportGeometry CurrentDirac
  DiracCurrentBounds CurrentCompactElementaryPushforwards CurrentDegreeTransportIdentity
  CurrentJoinSealed CurrentJoinConvexSupport OrientedSimplexCurrentUP
  OrientedSimplexCurrentSealed
  OrientedSimplexCurrentLaws PolyhedralCurrentGenerators.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [oriented_simplex_current_convex_support]:
    a convex set containing every original vertex
    contains the whole current support, as used in
    Federer 4.1.32, p. 392. The ambient
    dimension and the simplex degree remain independent. *)
Theorem oriented_simplex_current_convex_support (R:realType)
    (h2:(1+1:R)!=0) n m (v:'I_(m.+1)->R_n R n)
    (H:set (R_n R n)) (hH:is_inner_convex H):
  (forall i,H (v i))->
  @current_support R h2 n (fun _=>True)
    (fun (x:R_n R n) (_:True)=>@norm_full_domain_interior R (R_n R n)
      (inner_norm (@euclidean_inner_productP R n)) x) m
    (@OrientedSimplexCurrent.value R h2 n m v) `<=` H.
Proof.
elim:m v=>[|m ih] v hVertices.
- rewrite oriented_simplex_current_point.
  move=>x hx;have hxPoint:=@dirac_current_support_subset R h2 n (fun _=>True)
    (fun (x:R_n R n) (_:True)=>@norm_full_domain_interior R (R_n R n)
      (inner_norm (@euclidean_inner_productP R n)) x) (v ord0) I x hx.
  by rewrite hxPoint.
- pose X:=R_n R n;pose NX:=inner_norm (@euclidean_inner_productP R n).
  pose Full:set X:=fun _=>True.
  pose hFull:=fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x.
  pose P:=@dirac_current R h2 n Full hFull (v ord0).
  pose T:=@OrientedSimplexCurrent.value R h2 n m (current_simplex_tail v).
  pose hP:=@current_compact_dirac_support R h2 n Full hFull (v ord0) I.
  pose hT:=@oriented_simplex_current_compact R h2 n m (current_simplex_tail v).
  have hSimplex:=@oriented_simplex_current_successor R h2 n m v hP hT.
  rewrite current_degree_transport_identity in hSimplex.
  rewrite hSimplex;apply:(@current_join_convex_support R h2 n 0%N m P T hP hT H hH).
  + move=>x hx;have hxPoint:=@dirac_current_support_subset R h2 n Full hFull
      (v ord0) I x hx;by rewrite hxPoint.
  + exact:ih (current_simplex_tail v) (fun i=>hVertices (lift ord0 i)).
Qed.

(** Source for [oriented_simplex_current_hull_support]:
    the literal original vertex hull carries the actual
    simplex current, used for the projective-image and
    halfspace arguments in 4.1.32, pp. 392–393. *)
Theorem oriented_simplex_current_hull_support (R:realType)
    (h2:(1+1:R)!=0) n m (v:'I_(m.+1)->R_n R n):
  @current_support R h2 n (fun _=>True)
    (fun (x:R_n R n) (_:True)=>@norm_full_domain_interior R (R_n R n)
      (inner_norm (@euclidean_inner_productP R n)) x) m
    (@OrientedSimplexCurrent.value R h2 n m v) `<=`
      @polyhedral_simplex_vertex_hull R n m v.
Proof.
apply:oriented_simplex_current_convex_support;first exact:convex_hull_convex.
move=>i;apply:convex_hull_includes;by exists i.
Qed.
