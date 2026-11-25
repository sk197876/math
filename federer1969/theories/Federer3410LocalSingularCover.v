(** Federer (1969), 3.4.10, p. 337:
    every point of the original domain has
    a neighbourhood on which the nonregular part
    is covered by finitely many analytic manifolds
    of dimension less than the actual global dimension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness AnalyticVarietyGermUP
  AnalyticSetLocalDepth AnalyticSetDimension BoundedNaturalSupremumUP
  AnalyticSetNonemptyCentres AnalyticRegularLocusUP AnalyticRegularLocusSealed
  AnalyticSubmanifoldUP AnalyticCentreSingularManifoldCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [federer_3_4_10_local_singular_cover]: the
    finite local cover behind the globally locally
    finite family in 3.4.10, p. 337.
    At points outside the original analytic set,
    its proved relative closedness supplies an empty
    local cover. The regular part remains opaque. *)
Theorem federer_3_4_10_local_singular_cover (R:realType) n (U S:set (R_n R n)) u:
  let X:=R_n R n in
  let hB:=@euclidean_inner_productP R n in
  let hNX:=inner_norm_real_norm hB in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  @open T U ->S `<=` U ->
  @is_analytic_set_in R X (inner_norm hB) hNX U S ->
  @analytic_set_dimension R n S=u.+1 ->
  forall a,U a ->exists W:set X,exists F:set (set X),
    @open T W /\W a /\W `<=` U /\finite_set F /\
    (forall P,F P ->exists d,(d<u.+1)%N /\@is_euclidean_analytic_submanifold R n d P) /\
    (S `\` @AnalyticRegularLocus.value R n u.+1 U S) `&` W `<=` \bigcup_(P in F) P.
Proof.
move=>X hB hNX T hU hSU hAnalytic hDimension a haU.
case:(pselect (S a))=>haS.
- have hBound:(@analytic_set_local_depth R n S a<=u.+1)%N.
    rewrite -hDimension.
    exact:(@bounded_natural_supremum_upper X S (@analytic_set_local_depth R n S)
      (@analytic_set_dimension R n S) (@analytic_set_dimension_laws R n S) a haS).
  exact:(@analytic_centre_singular_manifold_cover R n U S
    (@AnalyticRegularLocus.value R n u.+1 U S) a u hU haU
    (hAnalytic a haU) hBound (@AnalyticRegularLocus.laws R n u.+1 U S)).
- have [V [hV [hVa hEmpty]]]:=@analytic_set_outside_empty_neighbourhood R X
    (inner_norm hB) hNX U S a hAnalytic haU haS.
  exists (U `&` V),set0;split;first exact:openI hU hV.
  split;first by split.
  split;first by move=>x hx;exact:hx.1.
  split;first exact:finite_set0.
  split;first by move=>P.
  move=>x [[hxS _] [_ hxV]];have h:(S `&` V) x by split.
  by rewrite hEmpty in h.
Qed.
