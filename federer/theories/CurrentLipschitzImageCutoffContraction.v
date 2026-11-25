(** Federer (1969), 4.1.14, p. 371: one
    source cutoff valid above a compact target
    cutoff identifies the corresponding contracted image
    current. Only the original local-image action,
    scalar contraction and support of products
    are used. No nonsmooth cutoff pullback is
    claimed to be a smooth scalar test. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms AlternatingZero LipschitzUP CurrentSpaces CurrentSupportGeometry
  CurrentContraction CurrentEvaluation CurrentTestFormProduct
  CurrentTestFormProductLeftSupport SmoothTestSpaces FlatCurrentsUP
  CurrentLipschitzPushforwardUP CurrentFlatLipschitzPushforwardSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_lipschitz_image_cutoff_contraction]:
    the original image contracted with gamma
    equals the compact source localization image
    contracted with the same gamma, supporting
    composition in Federer 4.1.14, p. 371.
    The source cutoff is one near the
    relevant support over spt gamma; there is
    no differentiability premise on f. *)
Theorem current_lipschitz_image_cutoff_contraction
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
    (T:@current_space R h2 n U hU m)
    (hT:@is_locally_flat_current R h2 n m U hU T)
    (Q:@current_space R h2 nu V hV m)
    (hQ:@is_current_lipschitz_image R h2 n nu m U V hU hV
      f hImage hLocal T Q)
    (gamma:@current_test_space R h2 nu V hV 0%N)
    (delta:@current_test_space R h2 n U hU 0%N):
  (forall x,@current_support R h2 n U hU m T x ->
    @current_test_support R h2 nu 0%N V hV gamma (f x) ->
    @interior (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n)))
      [set z|@current_test_value R h2 n U hU 0%N delta z=
        @zero_form R (R_n R n) R^o 1] x) ->
  @current_contraction R h2 nu 0%N m V hV
    (smooth_test_inclusion (@current_smooth_space_laws R h2 nu V hV 0%N) gamma) Q=
  @current_contraction R h2 nu 0%N m V hV
    (smooth_test_inclusion (@current_smooth_space_laws R h2 nu V hV 0%N) gamma)
    (@CurrentFlatLipschitzPushforward.value R h2 n nu m U V hU hV f hImage hLocal
      (@current_contraction R h2 n 0%N m U hU
        (smooth_test_inclusion (@current_smooth_space_laws R h2 n U hU 0%N) delta) T)
      (hT delta)).
Proof.
move=>hDelta;apply:(@current_values_extensional R h2 nu m V hV)=>psi.
rewrite !current_contraction_evaluation.
apply:hQ.2.
move=>x hx hProduct.
apply:(hDelta x hx).
exact:(@current_test_form_product_left_support R h2 nu 0%N m V hV gamma psi
  (f x) hProduct).
Qed.
