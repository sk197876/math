(** Federer (1969), 4.1.14, pp. 371–372: independently
    specify the affine chain when the segment-image condition
    holds only over spt T. Every original open time/source
    neighbourhood gives the same actual interval-product image.
    Existence, neighbourhood independence and uniqueness are
    separate theorems; no chosen neighbourhood is exposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct LipschitzUP EuclideanBlockLinearMaps
  CurrentSpaces CurrentOpenRestriction CurrentHomotopyUP CurrentHomotopyDomain
  CurrentHomotopyTimeSegment CurrentCartesianDomain CurrentCartesianProductSealed
  CurrentAffineHomotopySealed CurrentAffineHomotopyClass
  CurrentAffineHomotopyLocalLipschitz CurrentApproximationOpenRestriction
  FlatCurrentsUP CurrentFlatLipschitzPushforwardSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_affine_neighbourhood_product]: the literal
    [0,1] times R_WT on A times W, supporting
    Federer 4.1.14, pp. 371–372. It is the previously
    specified Cartesian product and original interval current. *)
Definition current_affine_neighbourhood_product (R:realType)
    (h2:(1+1:R)!=0) n m (A:set R)
    (hA:@is_homotopy_parameter_interval R A)
    (U W:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hW:forall x,W x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) W x)
    (hWU:forall x,W x->U x)
    (T:@current_space R h2 n U hU m) :=
  @CartesianCurrentProduct.value R h2 1%N n 1%N m
    (@current_homotopy_time_domain R A) W
    (@current_homotopy_time_domain_open R A hA) hW
    (@current_homotopy_time_segment R A hA h2)
    (@current_open_restriction R h2 n m W U hW hU hWU T).

(** Source for [current_affine_neighbourhood_image]: the original
    affine image condition on a derived open time-space
    neighbourhood, supporting Federer 4.1.14, p. 371. *)
Definition current_affine_neighbourhood_image (R:realType) n nu
    (A:set R) (W:set (R_n R n)) (V:set (R_n R nu))
    (f g:R_n R n->R_n R nu)
    (hBand:forall t x,A t->W x->V ((1-t)*:f x+t*:g x)) :
    forall z,@current_homotopy_product_domain R n A W z->
      V (@CurrentAffineHomotopy.value R n nu f g z).
Proof.
move=> z [ht hx]; rewrite current_affine_homotopy_coordinates.
exact: hBand _ _ ht hx.
Defined.

(** Source for [current_affine_neighbourhood_local]: the actual
    affine map has the original local Lipschitz class on
    every such product, supporting Federer 4.1.14, p. 371. *)
Definition current_affine_neighbourhood_local (R:realType) n nu
    (U W:set (R_n R n))
    (hW:forall x,W x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) W x)
    (hWU:forall x,W x->U x)
    (f g:R_n R n->R_n R nu)
    (hFLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (hGLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U g)
    (A:set R) (hA:@is_homotopy_parameter_interval R A) :=
  @current_affine_homotopy_locally_lipschitz R n nu f g A hA W hW
    (@metric_local_lipschitz_domain_restriction R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu)))
      U W f hWU hFLocal)
    (@metric_local_lipschitz_domain_restriction R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu)))
      U W g hWU hGLocal).

Section CurrentAffineNeighbourhoodPushforward.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Variables (U:set (R_n R n)) (V:set (R_n R nu)).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Hypothesis hV:forall y,V y->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R nu)) V y.
Variables f g:R_n R n->R_n R nu.
Hypotheses (hFLocal:@is_locally_metric_lipschitz R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
  (hGLocal:@is_locally_metric_lipschitz R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U g).
Variable T:@current_space R h2 n U hU m.

(** Source for [current_affine_neighbourhood_pushforward]: the
    actual original affine interval-product image on A times W,
    supporting Federer 4.1.14, pp. 371–372. This alias
    uses only the public opaque compact flat pushforward. *)
Definition current_affine_neighbourhood_pushforward
    (A:set R) (hA:@is_homotopy_parameter_interval R A)
    (W:set (R_n R n))
    (hW:forall x,W x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) W x)
    (hWU:forall x,W x->U x)
    (hBand:forall t x,A t->W x->V ((1-t)*:f x+t*:g x))
    (hProduct:@is_flat_current R h2 (1+n)%N (1+m)%N
      (@current_homotopy_product_domain R n A W)
      (@current_cartesian_domain_open R 1%N n (@current_homotopy_time_domain R A)
        W (@current_homotopy_time_domain_open R A hA) hW)
      (@current_affine_neighbourhood_product R h2 n m A hA U W hU hW hWU T)) :=
  @CurrentFlatLipschitzPushforward.value R h2 (1+n)%N nu (1+m)%N
    (@current_homotopy_product_domain R n A W) V
    (@current_cartesian_domain_open R 1%N n (@current_homotopy_time_domain R A)
      W (@current_homotopy_time_domain_open R A hA) hW) hV
    (@CurrentAffineHomotopy.value R n nu f g)
    (@current_affine_neighbourhood_image R n nu A W V f g hBand)
    (@current_affine_neighbourhood_local R n nu U W hW hWU f g hFLocal hGLocal A hA)
    (@current_affine_neighbourhood_product R h2 n m A hA U W hU hW hWU T) hProduct.
End CurrentAffineNeighbourhoodPushforward.

(** Source for [is_current_lipschitz_affine_chain]: the original
    h#([0,1] times T) in Federer 4.1.14, p. 372,
    agrees with the original compact flat image on every
    allowed open support neighbourhood. Flat membership of each
    interval product is quantified as evidence, and is derived
    internally in the existence theorem. No support-coincidence
    theorem or chosen smoothing family enters the definition. *)
Definition is_current_lipschitz_affine_chain (R:realType)
    (h2:(1+1:R)!=0) n nu m (U:set (R_n R n)) (V:set (R_n R nu))
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
    (Q:@current_space R h2 nu V hV (1+m)%N) : Prop :=
  @is_flat_current R h2 nu (1+m)%N V hV Q /\
  forall (A:set R) (hA:@is_homotopy_parameter_interval R A)
    (W:set (R_n R n))
    (hW:forall x,W x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) W x)
    (hWU:forall x,W x->U x)
    (hSupport:@current_support R h2 n U hU m T `<=` W)
    (hBand:forall t x,A t->W x->V ((1-t)*:f x+t*:g x))
    (hProduct:@is_flat_current R h2 (1+n)%N (1+m)%N
      (@current_homotopy_product_domain R n A W)
      (@current_cartesian_domain_open R 1%N n (@current_homotopy_time_domain R A)
        W (@current_homotopy_time_domain_open R A hA) hW)
      (@current_affine_neighbourhood_product R h2 n m A hA U W hU hW hWU T)),
    Q=@current_affine_neighbourhood_pushforward R h2 n nu m U V hU hV
      f g hFLocal hGLocal T A hA W hW hWU hBand hProduct.
