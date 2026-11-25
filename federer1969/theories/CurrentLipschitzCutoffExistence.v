(** Federer (1969), 4.1.14, p. 371: properness
    on the actual support supplies the original scalar
    cutoff for each compact family of target tests.
    The same construction is used in 4.1.7, p. 359;
    it requires no smoothness or global properness of f. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms AlternatingZero CurrentSpaces CurrentSupportGeometry SmoothCompactSet CurrentScalarCutoffs
  CurrentProperSupport CurrentLipschitzPushforwardUP SmoothTestSpaces SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_lipschitz_compact_target_cutoff]:
    one gamma is admissible for every original target
    test supported in a given compact K, supporting
    Federer 4.1.14, p. 371. Only f restricted to
    spt T is assumed proper. Empty compact loci
    and empty source or target are retained. *)
Theorem current_lipschitz_compact_target_cutoff
    (R:realType) (h2:(1+1:R)!=0) n nu m
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (T:@current_space R h2 n U hU m)
    (f:R_n R n->R_n R nu) (hImage:forall x,U x->V (f x))
    (hProper:@is_current_proper_on_support R h2 n nu m U hU V T f hImage)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R nu)) V):
  exists gamma:@current_test_space R h2 n U hU 0%N,
    forall phi:@current_test_space R h2 nu V hV m,
      @current_test_support R h2 nu m V hV phi `<=` smooth_compact_carrier K ->
      @is_current_lipschitz_pushforward_cutoff R h2 n nu m U V hU hV T f phi gamma.
Proof.
pose L:=@current_proper_support_compact_locus R h2 n nu m U hU V T f hImage hProper K.
have[gamma [W [hW [hLW [hWU hOne]]]]]:=@current_compact_scalar_cutoff R h2 n U hU L.
exists gamma=>phi hPhi x hx hSupportPhi.
have hL:smooth_compact_carrier L x:=conj hx (hPhi (f x) hSupportPhi).
have hPoint:W x:=hLW x hL.
have hNeighbourhood:@nbhs _ (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n))) x W.
  exact:open_nbhs_nbhs (conj hW hPoint).
apply:(filterS _ hNeighbourhood)=>z hz.
exact:hOne z hz.
Qed.
