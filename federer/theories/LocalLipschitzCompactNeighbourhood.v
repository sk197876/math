(** Federer (1969), 4.1.24, p. 380: the target
    map is only locally Lipschitz on its original open
    domain. Near its compact K it has one global
    finite Lipschitz bound. Derive a compact neighbourhood
    inside that original domain, then use the earlier
    compact local-to-global bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  NormBoundedLinearTopology InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates
  LipschitzUP LipschitzBasic SmoothCompactSet SmoothCompactNeighbourhoods
  OpenLocalLipschitzCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [local_lipschitz_compact_neighbourhood]: the
    globally Lipschitz neighbourhood needed to preserve the
    literal rectifiable approximation witnesses under the
    original locally Lipschitz g in 4.1.24, p. 380.
    No extension of g, convexity, or nonempty-K premise
    is imposed. Empty U and K are allowed. *)
Theorem local_lipschitz_compact_neighbourhood (R:realType) n nu
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (g:R_n R n->R_n R nu):
  @is_locally_metric_lipschitz R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U g->
  exists W:set (R_n R n),
    (forall x,W x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) W x) /\
    smooth_compact_carrier K `<=` W /\ W `<=` U /\
    @is_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) W g.
Proof.
move=>hLocal.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose NY:=inner_norm (@euclidean_inner_productP R nu).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R nu).
pose XT:=real_norm_metric_space hNX.
have[E hInterior]:=@smooth_compact_neighbourhood_exists R X NX hNX n
  (@coordinate_basis R n) (@coordinate_basisP R n) U hU K.
pose W:set X:=@interior XT (smooth_compact_carrier E).
have hOpen:@open XT W:=@open_interior XT (smooth_compact_carrier E).
have hW:forall x,W x->norm_domain_interior NX W x.
  move=>x hx;apply:(@norm_domain_interior_neighbourhood R X NX hNX W x).2.
  exact:open_nbhs_nbhs (conj hOpen hx).
have hKW:smooth_compact_carrier K `<=` W.
  move=>x hx;exact:(@norm_domain_interior_neighbourhood R X NX hNX
    (smooth_compact_carrier E) x).1 (hInterior x hx).
have hWE:W `<=` smooth_compact_carrier E:=@interior_subset XT _.
have hWU:W `<=` U.
  move=>x hx;exact:smooth_compact_in_domain E x (hWE x hx).
have[L [hL hBound]]:=@norm_open_local_lipschitz_compact R X (R_n R nu)
  NX NY hNX hNY U g (smooth_compact_carrier E) hU hLocal
  (smooth_compact_is_compact E) (smooth_compact_in_domain E).
exists W;split;first exact:hW.
split;first exact:hKW.
split;first exact:hWU.
exists L;split;first exact:hL.
exact:(@metric_lipschitz_bound_restrict R (real_norm_metric_space hNX)
  (real_norm_metric_space hNY) (smooth_compact_carrier E) W
  g L hWE hBound).
Qed.
