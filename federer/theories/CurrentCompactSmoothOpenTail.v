(** Federer (1969), 4.1.14, pp. 370–372: a chosen
    compact smooth family may be restricted to a common
    smaller source and a common tail. The same finite
    derivative cap and the exact original compact carrier
    are retained. These are ordinary allowed approximants;
    no new universal image premise is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentCompactSmoothApproximationUP CurrentLipschitzCompactImage
  CurrentSmoothApproximationUP SmoothClassOpenRestriction
  CurrentMapDifferentialOpenRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_compact_smooth_open_tail]: the original
    common-source and common-tail approximation used for the
    affine homotopy in Federer 4.1.14, pp. 371–372.
    The source restriction preserves actual derivatives by
    the preceding locality law of 3.1.1, pp. 209–210. *)
Theorem current_compact_smooth_open_tail (R:realType) n nu
    (U:set (R_n R n)) (V:set (R_n R nu))
    (K L:smooth_compact_set
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (hKL:smooth_compact_carrier K `<=` smooth_compact_carrier L)
    (f:R_n R n->R_n R nu) (c:R) (Z W:set (R_n R n))
    (hW:forall x,W x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) W x)
    (hWZ:W `<=` Z) (hKW:smooth_compact_carrier K `<=` W)
    (a:nat->R_n R n->R_n R nu) (N:nat):
  @is_current_compact_smooth_approximation R n nu U V L f c Z a->
  @is_current_smooth_approximation R n nu W V
    (@current_compact_index_in_open R n U W K hKW) f (fun i=>a (N+i)%N).
Proof.
move=>hApprox;constructor.
- move=>i x hx;exact:(@current_compact_smooth_image R n nu U V L f c Z a
    hApprox (N+i)%N x (hWZ x hx)).
- move=>i;exact:(@smooth_class_open_restriction R (R_n R n) (R_n R nu)
    (inner_norm (@euclidean_inner_productP R n))
    (inner_norm (@euclidean_inner_productP R nu))
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R nu)) Z W (a (N+i)%N)
    hWZ hW (current_compact_smooth_class hApprox (N+i)%N)).
- exists c;split;first exact:current_compact_smooth_bound_nonnegative hApprox.
  move=>i x hx.
  rewrite (@current_map_differential_open_restriction R n nu W Z hW hWZ
    (a (N+i)%N) (current_compact_smooth_class hApprox (N+i)%N) x (hKW x hx)).
  exact:(@current_compact_smooth_differential_bound R n nu U V L f c Z a
    hApprox (N+i)%N x (hWZ x (hKW x hx))).
- move=>eps hEps.
  have[M hM]:=current_compact_smooth_uniform hApprox hEps.
  exists M=>i hi x hx.
  exact:hM (N+i)%N (leq_trans hi (leq_addl N i)) x (hKL x hx).
Qed.
