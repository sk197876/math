(** Federer (1969), 4.1.12, p. 368: the
    original dyadic endpoints with zero form a
    compact subset of the actual Euclidean line.
    Its isolated-point geometry excludes every nonzero
    normal one-current. Reuse the original scalar
    coordinate maps and the proved point-support argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate InnerNorm HilbertFormCompactness
  RealMetricBackground SmoothCompactSet ScalarCurrentIntervalCompact DyadicEndpointSupportGeometry
  CurrentSpaces NormalCurrentsUP CurrentNormalSingleDerivedSupportZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DyadicCurrentEndpointCompact.
Variable R:realType.
Local Notation X := (R_n R 1%N).
Local Notation N := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation XT := (real_norm_metric_space hN).

(** Source for [dyadic_current_endpoint_carrier]: the
    actual original endpoint set {0} union {2^(-k):k>=1}
    in R^1, supporting Federer 4.1.12, p. 368.
    This is the given scalar coordinate identification. *)
Definition dyadic_current_endpoint_carrier:set X:=
  [set x|dyadic_endpoint_set R (euclidean_one_project x)].

(** Source for [dyadic_current_endpoint_carrier_compact]: the
    literal original endpoint set is compact in the
    actual current-source topology, supporting Federer
    4.1.12, p. 368. *)
Theorem dyadic_current_endpoint_carrier_compact:@compact XT dyadic_current_endpoint_carrier.
Proof.
have hImage:(fun t:real_line_metric R=>(euclidean_one_embed t:XT)) @` dyadic_endpoint_set R=
    dyadic_current_endpoint_carrier.
  apply/seteqP;split.
  - move=>x [t ht <-].
    change (dyadic_endpoint_set R (euclidean_one_project (euclidean_one_embed t))).
    by rewrite euclidean_one_embedK.
  - move=>x hx;exists (euclidean_one_project x);first exact:hx.
    exact:euclidean_one_projectK.
rewrite -hImage.
exact:(continuous_compact (continuous_subspaceT (@scalar_current_embed_continuous R))
  (dyadic_endpoint_set_compact R)).
Qed.

(** Source for [dyadic_current_endpoint_isolated]: every
    nonzero point of the actual original endpoint
    set is isolated in that set, supporting
    Federer 4.1.12, p. 368. Transport
    the proved scalar neighbourhood through the existing
    coordinate homeomorphism. *)
Theorem dyadic_current_endpoint_isolated y:
  dyadic_current_endpoint_carrier y->y<>euclidean_one_embed 0->
  exists W:set X,@open XT W /\W y /\
    forall z,dyadic_current_endpoint_carrier z->W z->z=y.
Proof.
move=>hY hNonzero.
have hScalar:euclidean_one_project y<>0.
  move=>hZero;apply:hNonzero;by rewrite -(euclidean_one_projectK y) hZero.
have[W [hW [hWy hUnique]]]:=@dyadic_endpoint_set_isolated R (euclidean_one_project y) hY hScalar.
exists ((@euclidean_one_project R) @^-1` W);split.
- exact:((@continuousP XT (real_line_metric R) (@euclidean_one_project R)).1
    (@scalar_current_project_continuous R) W hW).
- split;first exact:hWy.
  move=>z hz hWz;apply:(can_inj (@euclidean_one_projectK R)).
  exact:hUnique (euclidean_one_project z) hz hWz.
Qed.

(** Source for [dyadic_current_endpoint_compact]: the
    literal original compact endpoint index used for
    the flat-versus-mass closure obstruction in Federer
    4.1.12, p. 368. It selects no current. *)
Definition dyadic_current_endpoint_compact:smooth_compact_set hN (fun _:X=>True):=
  @Build_smooth_compact_set R X N hN (fun _=>True) dyadic_current_endpoint_carrier
    (fun _ _=>Logic.I) dyadic_current_endpoint_carrier_compact.
End DyadicCurrentEndpointCompact.
Arguments dyadic_current_endpoint_carrier (R): clear implicits.
Arguments dyadic_current_endpoint_compact (R): clear implicits.

(** Source for [dyadic_endpoint_normal_one_current_zero]: the
    original compact dyadic endpoint set supports no
    nonzero normal one-current, as asserted in Federer
    4.1.12, p. 368. Apply the original
    point-support and isolated-support results to its
    actual proved geometry, without assuming a density. *)
Theorem dyadic_endpoint_normal_one_current_zero (R:realType) (h2:(1+1:R)!=0)
    (T:@current_space R h2 1%N (fun _=>True)
      (fun x _=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x) 1%N):
  @is_normal_current R h2 1%N (fun _=>True)
    (fun x _=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x) 1%N T->
  @current_support R h2 1%N (fun _=>True)
    (fun x _=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x) 1%N T `<=`
    dyadic_current_endpoint_carrier R->T=0.
Proof.
move=>hNormal hSupport.
apply:(@current_normal_single_derived_support_zero R h2 (fun _=>True)
  (fun x _=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x)
  (dyadic_current_endpoint_carrier R) (euclidean_one_embed 0) _ T hNormal hSupport).
exact:(@dyadic_current_endpoint_isolated R).
Qed.
