(** Federer (1969), 4.1.14, p. 371: the original
    locally flat image is specified by the compact
    cutoff formula on every original target test.
    Preserve the precise interior plateau condition
    from 4.1.7, p. 359. Properness on the actual
    support is needed for existence, not for stating
    these independent action and local-flatness laws. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms AlternatingZero LipschitzUP CurrentSpaces CurrentSupportGeometry CurrentContraction
  SmoothTestSpaces FlatCurrentsUP CurrentFlatLipschitzPushforwardSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_current_lipschitz_pushforward_cutoff]:
    every x in spt T with f(x) in spt phi lies
    in Int{gamma=1}, Federer 4.1.14, p. 371,
    retaining the original convention of 4.1.7,
    p. 359. This condition asserts a plateau near
    the indicated set, not only pointwise values there. *)
Definition is_current_lipschitz_pushforward_cutoff
    (R:realType) (h2:(1+1:R)!=0) n nu m
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (T:@current_space R h2 n U hU m) (f:R_n R n->R_n R nu)
    (phi:@current_test_space R h2 nu V hV m)
    (gamma:@current_test_space R h2 n U hU 0%N):Prop:=
  forall x,@current_support R h2 n U hU m T x ->
    @current_test_support R h2 nu m V hV phi (f x) ->
    @interior (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n)))
      [set z|@current_test_value R h2 n U hU 0%N gamma z=
        @zero_form R (R_n R n) R^o 1] x.

(** Source for [is_current_lipschitz_image]: the original
    locally flat image and its literal formula for every
    admissible gamma, Federer 4.1.14, p. 371. The
    compact localizations are passed through the already
    specified opaque global flat image. No selected
    cutoff or source exhaustion is part of this definition. *)
Definition is_current_lipschitz_image
    (R:realType) (h2:(1+1:R)!=0) n nu m
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f:R_n R n->R_n R nu) (hImage:forall x,U x->V (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (T:@current_space R h2 n U hU m) (Q:@current_space R h2 nu V hV m):Prop:=
  @is_locally_flat_current R h2 nu m V hV Q /\
  forall (phi:@current_test_space R h2 nu V hV m)
    (gamma:@current_test_space R h2 n U hU 0%N)
    (hGamma:@is_flat_current R h2 n m U hU
      (@current_contraction R h2 n 0%N m U hU
        (smooth_test_inclusion (@current_smooth_space_laws R h2 n U hU 0%N) gamma) T)),
    @is_current_lipschitz_pushforward_cutoff R h2 n nu m U V hU hV T f phi gamma ->
    @current_value R h2 nu V hV m Q phi=
    @current_value R h2 nu V hV m
      (@CurrentFlatLipschitzPushforward.value R h2 n nu m U V hU hV f hImage hLocal
        (@current_contraction R h2 n 0%N m U hU
          (smooth_test_inclusion (@current_smooth_space_laws R h2 n U hU 0%N) gamma) T)
        hGamma) phi.
