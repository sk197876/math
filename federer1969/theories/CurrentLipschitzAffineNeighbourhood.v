(** Federer (1969), 4.1.14, pp. 371–372: the
    original support-only segment containment supplies an
    open time/source neighbourhood for the actual affine
    homotopy. Reuse the preceding continuous compact-product
    neighbourhood theorem and the original compact support. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP NormBoundedLinearTopology InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct LipschitzUP
  OpenLocalLipschitzCompact SmoothCompactSet CurrentSpaces FlatCurrentsUP
  CurrentLipschitzCompactImage CurrentHomotopyUP
  CurrentAffineHomotopyContinuousNeighbourhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_lipschitz_affine_neighbourhood_exists]:
    shrink around the actual support, as in 4.1.13,
    pp. 369–370, for the locally Lipschitz affine
    formula of Federer 4.1.14, pp. 371–372.
    The original flat index need not lie in W. *)
Theorem current_lipschitz_affine_neighbourhood_exists
    (R:realType) (h2:(1+1:R)!=0) n nu m
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f g:R_n R n->R_n R nu)
    (hFLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (hGLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U g)
    (T:@current_space R h2 n U hU m)
    (hFlat:@is_flat_current R h2 n m U hU T)
    (hBand:forall t x,0<=t<=1->@current_support R h2 n U hU m T x->
      V ((1-t)*:f x+t*:g x)) :
  exists A:set R,exists hA:@is_homotopy_parameter_interval R A,
  exists W:set (R_n R n),
  exists hW:forall x,W x->norm_domain_interior
    (inner_norm (@euclidean_inner_productP R n)) W x,
  exists hWU:forall x,W x->U x,
    (@current_support R h2 n U hU m T `<=` W) /\
    forall t x,A t->W x->V ((1-t)*:f x+t*:g x).
Proof.
pose X := R_n R n.
pose Y := R_n R nu.
pose NX := inner_norm (@euclidean_inner_productP R n).
pose NY := inner_norm (@euclidean_inner_productP R nu).
pose hNX := inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNY := inner_norm_real_norm (@euclidean_inner_productP R nu).
have [K hK] := hFlat.
have hCompact := @flat_supported_current_compact R h2 n m U hU K T hK.
pose Support := @Build_smooth_compact_set R X NX hNX U
  (@current_support R h2 n U hU m T) (fun x hx => hx.1) hCompact.
have hF := @norm_open_local_lipschitz_class_zero R X Y NX NY hNX hNY U f hU hFLocal.
have hG := @norm_open_local_lipschitz_class_zero R X Y NX NY hNX hNY U g hU hGLocal.
have [A [W [hA [hOpen [hSupport [hWU hImage]]]]]] :=
  @current_affine_homotopy_continuous_neighbourhood R n nu U V hU hV
    f g hF hG Support hBand.
have hW : forall x,W x->norm_domain_interior NX W x.
  move=> x hx; apply: (@norm_domain_interior_neighbourhood R X NX hNX W x).2.
  exact: open_nbhs_nbhs (conj hOpen hx).
exists A,hA,W,hW,hWU; exact: conj hSupport hImage.
Qed.
