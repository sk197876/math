(** Federer (1969), 4.1.14, p. 371: an original
    locally Lipschitz homotopy has locally Lipschitz slices
    and endpoints on the same original source. Use the
    bounded affine block inclusion of 4.1.8, p. 362,
    and the local composition law of 2.2.7, p. 64.
    No smoothness, global bound or new properness premise
    is needed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormClassOneUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate CurrentCartesianPointInclusion CurrentHomotopyUP
  CurrentHomotopyGeometry NormLocalLipschitzScalarProduct
  LipschitzUP MetricLocalLipschitzComposition OpenLocalLipschitzCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_local_lipschitz_domain_agreement]:
    equal original representatives on their relative domain
    have the same local distance bounds of 2.2.7,
    p. 64, as used for the homotopy endpoints in
    Federer 4.1.14, p. 371. *)
Theorem metric_local_lipschitz_domain_agreement (R:realType)
    (X Y:metricType R) (U:set X) (f g:X->Y):
  (forall x,U x->f x=g x)->
  @is_locally_metric_lipschitz R X Y U f->
  @is_locally_metric_lipschitz R X Y U g.
Proof.
move=>hEqual hF c hc.
have[W [hW [L [hL hBound]]]]:=hF c hc.
exists W;split;first exact:hW.
exists L;split;first exact:hL.
split;first exact:hBound.1.
move=>x y [hx hXW] [hy hYW].
rewrite -(@hEqual x hx) -(@hEqual y hy).
exact:hBound.2 x y (conj hx hXW) (conj hy hYW).
Qed.

Section CurrentLipschitzHomotopySlices.
Variable R:realType.
Variables n nu:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation Z:=(R_n R (1+n)%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation NZ:=(inner_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation hNZ:=(inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation XT:=(real_norm_metric_space hNX).
Local Notation YT:=(real_norm_metric_space hNY).
Local Notation ZT:=(real_norm_metric_space hNZ).
Variable A:set R.
Variables (U:set X) (V:set Y).
Variables (f g:X->Y) (h:Z->Y).
Hypothesis hGeometry:@is_current_homotopy_geometry R n nu A U V f g h.
Local Notation hA:=(@current_homotopy_parameter_interval R n nu A U V f g h hGeometry).
Local Notation hU:=(@current_homotopy_source_open R n nu A U V f g h hGeometry).
Local Notation AU:=(@current_homotopy_product_domain R n A U).
Local Notation slice:=(@current_homotopy_slice_map R n nu h).
Hypothesis hLocal:@is_locally_metric_lipschitz R ZT YT AU h.

(** Source for [current_lipschitz_homotopy_slice]: every
    original h_t is locally Lipschitz on U for t in
    the original open A, supporting Federer 4.1.14,
    p. 371. The conclusion includes dimension zero. *)
Theorem current_lipschitz_homotopy_slice t:
  A t->@is_locally_metric_lipschitz R XT YT U (slice t).
Proof.
move=>ht.
pose inclusion:=@current_cartesian_point_inclusion R 1%N n (@euclidean_one_embed R t).
have hSmooth:=@current_cartesian_point_inclusion_smooth R 1%N n U hU
  (@euclidean_one_embed R t).
have hInclusion:@is_locally_metric_lipschitz R XT ZT U inclusion.
  apply:(@norm_class_one_locally_metric_lipschitz R X Z NX NZ hNX hNZ U inclusion).
  exact:(@norm_class_firstP R X Z NX NZ hNX hNZ U inclusion).1 (hSmooth 1%N).
have hImage:forall x,U x->AU (inclusion x).
  move=>x hx;exact:(@current_homotopy_join_member R n A U t x ht hx).
exact:(@metric_local_lipschitz_composition R XT ZT YT U AU inclusion h
  hImage hInclusion hLocal).
Qed.

(** Source for [current_lipschitz_homotopy_endpoints]: the
    two original endpoints are locally Lipschitz by the
    original h_0=f and h_1=g equalities, supporting
    Federer 4.1.14, p. 371. Equality is needed
    only on the original U. *)
Theorem current_lipschitz_homotopy_endpoints:
  @is_locally_metric_lipschitz R XT YT U f /\
  @is_locally_metric_lipschitz R XT YT U g.
Proof.
split.
- apply:(@metric_local_lipschitz_domain_agreement R XT YT U (slice 0) f).
  + exact:(@current_homotopy_start R n nu A U V f g h hGeometry).
  + exact:(@current_lipschitz_homotopy_slice 0 (@homotopy_parameter_zero R A hA)).
- apply:(@metric_local_lipschitz_domain_agreement R XT YT U (slice 1) g).
  + exact:(@current_homotopy_end R n nu A U V f g h hGeometry).
  + exact:(@current_lipschitz_homotopy_slice 1 (@homotopy_parameter_one R A hA)).
Qed.

(** Source for [current_lipschitz_homotopy_endpoint_continuity]:
    the original locally Lipschitz endpoint maps are continuous
    on U, supporting the actual affine weight in Federer
    4.1.14, p. 371. This is derived, not added
    to the original homotopy hypotheses. *)
Corollary current_lipschitz_homotopy_endpoint_continuity:
  norm_class_zero NX NY U f /\norm_class_zero NX NY U g.
Proof.
have[hF hG]:=current_lipschitz_homotopy_endpoints.
split.
- exact:(@norm_open_local_lipschitz_class_zero R X Y NX NY hNX hNY U f hU hF).
- exact:(@norm_open_local_lipschitz_class_zero R X Y NX NY hNX hNY U g hU hG).
Qed.
End CurrentLipschitzHomotopySlices.
