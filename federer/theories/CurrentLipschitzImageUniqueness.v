(** Federer (1969), 4.1.14, p. 371: the literal
    compact-cutoff formula determines the original locally
    flat image uniquely. Properness only on spt T gives
    an admissible cutoff for each target test. No
    selected local image is used in this argument. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP SmoothCompactSet CurrentSpaces CurrentEvaluation FlatCurrentsUP
  SmoothTestEvaluation CurrentProperSupport CurrentLipschitzPushforwardUP
  CurrentLipschitzCutoffExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_lipschitz_image_unique]: equality
    on each original target test follows from one
    admissible gamma in the printed cutoff equation,
    Federer 4.1.14, p. 371. The two candidates
    satisfy the same independently stated laws. *)
Theorem current_lipschitz_image_unique
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
    (hProper:@is_current_proper_on_support R h2 n nu m U hU V T f hImage)
    (Q P:@current_space R h2 nu V hV m):
  @is_current_lipschitz_image R h2 n nu m U V hU hV f hImage hLocal T Q ->
  @is_current_lipschitz_image R h2 n nu m U V hU hV f hImage hLocal T P ->Q = P.
Proof.
move=>hQ hP;apply:(@current_values_extensional R h2 nu m V hV)=>phi.
have[K hK]:=smooth_test_support_bound (@current_smooth_space_laws R h2 nu V hV m) phi.
have[gamma hGamma]:=@current_lipschitz_compact_target_cutoff R h2 n nu m
  U V hU hV T f hImage hProper K.
have hCutoff:=hGamma phi hK.
exact:eq_trans (hQ.2 phi gamma (@hT gamma) hCutoff)
  (esym (hP.2 phi gamma (@hT gamma) hCutoff)).
Qed.
