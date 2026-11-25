(** Federer (1969), 4.1.12, p. 368, used for
    the source-neighbourhood passage in 4.1.14,
    pp. 370–372: a compact flat current has a
    flat compact index inside any open neighbourhood
    of its actual support. Reuse the exact earlier
    K-intersect-closure localisation. Do not replace
    the compact index by spt T itself. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormBoundedLinearTopology InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct FiniteCoordinates SmoothCompactSet SmoothCompactNeighbourhoods
  SmoothCompactClosureIntersection CurrentSpaces CurrentSupportGeometry
  FlatCurrentsUP FlatCurrentFinite FlatCurrentNeighbourhoodLocalisation CurrentLipschitzCompactImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [flat_current_compact_index_neighbourhood]:
    choose the original compact index inside a prescribed
    open neighbourhood of spt T, supporting Federer
    4.1.14, pp. 370–372, by the localisation in
    4.1.12, p. 368. Empty support needs no point choice. *)
Theorem flat_current_compact_index_neighbourhood
    (R:realType) (h2:(1+1:R)!=0) n m (U W:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hW:forall x,W x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) W x)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (T:@current_space R h2 n U hU m):
  @is_flat_current_supported_in R h2 n m U hU K T ->
  @current_support R h2 n U hU m T `<=` W ->
  exists L:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U,
    smooth_compact_carrier L `<=` W /\
    @is_flat_current_supported_in R h2 n m U hU L T.
Proof.
move=>hFlat hSupport.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose SK:=@Build_smooth_compact_set R X NX hNX W
  (@current_support R h2 n U hU m T) hSupport
  (@flat_supported_current_compact R h2 n m U hU K T hFlat).
have[E hE]:=@smooth_compact_neighbourhood_exists R X NX hNX n
  (@coordinate_basis R n) (@coordinate_basisP R n) W hW SK.
have hNeighbourhood x (hx:@current_support R h2 n U hU m T x):
    @nbhs _ (real_norm_metric_space hNX) x (smooth_compact_carrier E).
  exact:(@norm_domain_interior_neighbourhood R X NX hNX
    (smooth_compact_carrier E) x).1 (@hE x hx).
pose L:=@smooth_compact_closure_intersection R X NX hNX U K (smooth_compact_carrier E).
have hLocal:=@flat_current_neighbourhood_localisation R h2 n m U hU
  K T (smooth_compact_carrier E) hFlat hNeighbourhood.
exists L;split;last exact:hLocal.
have hClosed:@closed (real_norm_metric_space hNX) (smooth_compact_carrier E).
  exact:compact_closed (@metric_hausdorff R (real_norm_metric_space hNX))
    (smooth_compact_is_compact E).
move=>x hx.
have hClosure:@closure (real_norm_metric_space hNX) (smooth_compact_carrier E) x:=hx.2.
rewrite -((@closure_id (real_norm_metric_space hNX) (smooth_compact_carrier E)).1 hClosed)
  in hClosure.
exact:smooth_compact_in_domain E x hClosure.
Qed.
