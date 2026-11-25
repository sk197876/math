(** Federer (1969), 4.1.14, p. 371: the
    original compact flat image commutes with boundary.
    Use the same original compact index for T and
    its positive-degree boundary, and apply the proved
    original smooth-approximation boundary identity. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP SmoothCompactSet CurrentSpaces CurrentBoundary FlatCurrentsUP
  FlatCurrentBoundary CurrentCompactLipschitzImageBoundary
  CurrentFlatLipschitzPushforwardSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_flat_lipschitz_pushforward_boundary]:
    boundary(f#T)=f#(boundary T), Federer 4.1.14,
    p. 371. The original input is any compact
    flat current of positive degree; neither normality
    nor finite mass of T or its boundary is assumed. *)
Theorem current_flat_lipschitz_pushforward_boundary
    (R:realType) (h2:(1+1:R)!=0) n nu d
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f:R_n R n->R_n R nu) (hImage:forall x,U x->V (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (T:@current_space R h2 n U hU d.+1)
    (hT:@is_flat_current R h2 n d.+1 U hU T)
    (hBoundary:@is_flat_current R h2 n d U hU (@current_boundary R h2 n d U hU T)):
  @current_boundary R h2 nu d V hV
    (@CurrentFlatLipschitzPushforward.value R h2 n nu d.+1 U V hU hV
      f hImage hLocal T hT)=
    @CurrentFlatLipschitzPushforward.value R h2 n nu d U V hU hV
      f hImage hLocal (@current_boundary R h2 n d U hU T) hBoundary.
Proof.
have[K hKT]:=hT.
have hKB:=@flat_current_boundary_supported R h2 n d U hU K T hKT.
exact:(@current_compact_lipschitz_image_boundary R h2 n nu d U V hU hV
  f hImage hLocal K T hKT _ _
  ((@CurrentFlatLipschitzPushforward.laws R h2 n nu d.+1 U V hU hV
    f hImage hLocal T hT).2 K hKT)
  ((@CurrentFlatLipschitzPushforward.laws R h2 n nu d U V hU hV
    f hImage hLocal (@current_boundary R h2 n d U hU T) hBoundary).2 K hKB)).
Qed.
