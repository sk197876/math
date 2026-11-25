(** Federer (1969), 4.1.11, p. 366: the
    full original simplicial prism decomposition. Follow
    the printed induction: compare boundaries using the
    source faces, apply 4.1.10 in positive top degree,
    then transfer through the original affine parametrisations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate
  CurrentSpaces CurrentSegmentMapUP OrientedSegmentCurrentSealed CurrentCartesianPointInclusion
  CurrentAmbientCartesianProduct CurrentSimplexFrame OrientedSimplexCurrentUP OrientedSimplexCurrentSealed
  CurrentPrismVerticesSealed CurrentSimplexPrismSum CurrentSimplexPrismPoint
  CurrentSimplexPrismBoundaryComparison CurrentSimplexPrismTop CurrentSimplexPrismAffineTransfer.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentSimplexPrism.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).

(** Source for [current_simplex_prism]: the original
    [a,b] times [u_0,...,u_m] is the sum over
    k=0,...,m of (-1)^k times the simplex with
    vertices (a,u_0),...,(a,u_k),(b,u_k),...,(b,u_m),
    Federer 4.1.11, p. 366. The two Euclidean
    factor dimensions are arbitrary. Coincident endpoints,
    repeated vertices and degree zero are retained. *)
Theorem current_simplex_prism m:
  forall p n (a b:R_n R p) (v:'I_(m.+1)->R_n R n),
  @current_ambient_cartesian_product R h2 p n 1%N m
    (@OrientedSegmentCurrent.value R h2 p (Full p) (hFull p) a b
      (fun (t:R) (_:t \in `[0,1])=>Logic.I))
    (@OrientedSimplexCurrent.value R h2 n m v)=
  @current_simplex_prism_sum R h2 n (p+n)%N
    (@current_cartesian_point_inclusion R p n a)
    (@current_cartesian_point_inclusion R p n b) m v.
Proof.
elim:m=>[|m ih] p n a b v.
- exact:(@current_simplex_prism_point R h2 p n a b v).
- pose w:=@current_standard_simplex_vertices R m.+1.
  pose e0:=@euclidean_one_embed R 0.
  pose e1:=@euclidean_one_embed R 1.
  have hBoundary:=@current_simplex_prism_boundary_comparison R h2 1%N m.+1 m e0 e1 w
    (fun k=>ih 1%N m.+1 e0 e1 (current_simplex_face w k)).
  have hSource:=@current_simplex_prism_top R h2 1%N m.+1 m.+1 e0 e1 w
    (add1n m.+1) hBoundary.
  exact:(@current_simplex_prism_affine_transfer R h2 m.+1 w
    (@current_standard_simplex_nondegenerate R m.+1) p n a b v hSource).
Qed.

(** Source for [current_simplex_prism_formula]: the literal
    finite signed simplex sum in the printed prism
    display, Federer 4.1.11, p. 366. The opaque
    vertex map has exactly the independently specified
    original lower and upper ordered ranges. *)
Theorem current_simplex_prism_formula m p n (a b:R_n R p) (v:'I_(m.+1)->R_n R n):
  @current_ambient_cartesian_product R h2 p n 1%N m
    (@OrientedSegmentCurrent.value R h2 p (Full p) (hFull p) a b
      (fun (t:R) (_:t \in `[0,1])=>Logic.I))
    (@OrientedSimplexCurrent.value R h2 n m v)=
  \sum_(k<m.+1) (-1:R)^+k*:@OrientedSimplexCurrent.value R h2 (p+n)%N m.+1
    (@CurrentPrismVertices.value (R_n R n) (R_n R (p+n)%N)
      (@current_cartesian_point_inclusion R p n a)
      (@current_cartesian_point_inclusion R p n b) m v k).
Proof. exact:(@current_simplex_prism m p n a b v). Qed.
End CurrentSimplexPrism.
