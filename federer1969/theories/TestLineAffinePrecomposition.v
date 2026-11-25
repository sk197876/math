(** Federer (1969), 4.1.3, p. 348: translating and
    dilating the separated kernel preserves one-variable tests.
    An affine inverse carries the original compact support.
    Smoothness follows from the original class-infinity calculus. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology ring.
From Federer Require Import Hom TensorUP RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  NormRegularity NormRegularityOperations NormClassZeroTopology SmoothCompactSet
  SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation SmoothTestRepresentation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TestLineAffinePrecomposition.
Variable R:realType.
Local Notation hR := (@scalar_absolute_value_norm R).
Variable A:lmodType R.
Variable av:A->R^o->R^o.
Hypothesis hA:is_smooth_function_space hR hR (fun _=>True) av.
Variable gamma:smooth_test_space hA.
Variables c z:R.
Hypothesis hc:c!=0.

(** Source for [test_line_affine_precomposition_exists]: the
    actual affine factors of a translated dilated product kernel
    remain in D(R,R), supporting Federer 4.1.3, p. 348. *)
Theorem test_line_affine_precomposition_exists:
  exists f:smooth_test_space hA,forall t:R,
    smooth_test_value hA f t=smooth_test_value hA gamma (c*(t-z)).
Proof.
have hFull t (_:True):norm_domain_interior (fun t:R^o=>`|t|) (fun _=>True) t.
  exact:norm_full_domain_interior.
have hIdBound:norm_bounded_linear (fun t:R^o=>`|t|) (fun t:R^o=>`|t|)
    (hom_of_linear (linear_id R^o)).
  exists 1; split; first exact:ler01; by move=>t; rewrite mul1r.
have hId k:=@norm_class_linear R R^o R^o _ _ hR hR (fun _=>True)
  (hom_of_linear (linear_id R^o)) k hFull hIdBound.
have hAffine k:norm_class hR hR (fun _=>True) (fun t:R^o=>(c*(t-z):R^o)) k.
  have hC:=@norm_class_constant R R^o R^o _ _ hR hR (fun _=>True) z k hFull.
  exact:(norm_class_scale c (norm_class_subtract (hId k) hC)).
have hSmooth:norm_class_all_orders hR hR (fun _=>True)
    (fun t:R^o=>smooth_test_value hA gamma (c*(t-z))).
  move=>k; exact:(@norm_class_compose_on R R^o R^o R^o _ _ _ hR hR hR
    (fun _=>True) (fun _=>True) (fun t:R^o=>(c*(t-z):R^o))
    (smooth_test_value hA gamma) k (fun _ _=>I) (hAffine k) (smooth_test_value_smooth hA gamma k)).
pose inverse:=fun t:R^o=>(z+c^-1*t:R^o).
have hInverse:continuous (inverse:real_norm_metric_space hR->real_norm_metric_space hR).
  have hC:=@norm_class_constant R R^o R^o _ _ hR hR (fun _=>True) z 0%N hFull.
  have hClass:=norm_class_add hC (norm_class_scale c^-1 (hId 0%N)).
  move=>t; exact:(@norm_class_zero_continuous_at R R^o R^o _ _ hR hR
    (fun _=>True) inverse t (norm_class_continuous hClass) I).
have[K hK]:=smooth_test_support_bound hA gamma.
pose C:set R^o:=inverse @` smooth_compact_carrier K.
have hCompact:compact [set t:real_norm_metric_space hR|C t].
  exact:(continuous_compact (continuous_subspaceT hInverse) (smooth_compact_is_compact K)).
pose L:=@Build_smooth_compact_set R R^o _ hR (fun _=>True) C (fun _ _=>I) hCompact.
have hOff t:~smooth_compact_carrier L t ->
    smooth_test_value hA gamma (c*(t-z))=0.
  move=>ht; apply:contrapT=>hNonzero; apply:ht.
  have hIn:smooth_compact_carrier K (c*(t-z)).
    apply:hK; split; first exact I.
    exact:(@subset_closure (real_norm_metric_space hR)
      [set u|smooth_test_value hA gamma u<>0] (c*(t-z)) hNonzero).
  exists (c*(t-z)); first exact hIn.
  rewrite /inverse mulrA mulVf // mul1r; ring.
have[f hf]:=@smooth_test_represents_compact_function R R^o R^o _ _ hR hR
  (fun _=>True) A av hA L _ hSmooth hOff.
exists f=>t; exact:(hf t I).
Qed.
End TestLineAffinePrecomposition.
