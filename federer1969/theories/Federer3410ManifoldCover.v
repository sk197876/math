(** Federer (1969), 3.4.10, p. 337:
    the actual nonregular part is covered by
    analytic manifolds of strictly smaller dimension,
    and each compact subset of the original
    domain meets only finitely many members.
    Dimension zero is included through its empty
    nonregular part. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness InnerNormTopologyAdapters
  AnalyticVarietyGermUP AnalyticSetDimension AnalyticRegularLocusSealed
  AnalyticSubmanifoldUP Federer3410ZeroRegular Federer3410LocalSingularCover
  EuclideanLocallyFiniteManifoldCover LocallyFiniteFamilyUP LocallyFiniteFamilyCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [federer_3_4_10_manifold_cover]: the
    original manifold-cover assertion of 3.4.10,
    p. 337, with its literal finite
    incidence condition for every compact C in U.
    The set covered is the difference from
    the original opaque regular part, which is
    not assumed to be analytic. *)
Theorem federer_3_4_10_manifold_cover (R:realType) n (U S:set (R_n R n)) m:
  let X:=R_n R n in
  let hB:=@euclidean_inner_productP R n in
  let hNX:=inner_norm_real_norm hB in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  let E:=inner_metric_space hB in
  @open T U ->S `<=` U ->
  @is_analytic_set_in R X (inner_norm hB) hNX U S ->
  @analytic_set_dimension R n S=m ->
  exists F:set (set X),
    S `\` @AnalyticRegularLocus.value R n m U S `<=` \bigcup_(P in F) P /\
    (forall P,F P ->exists d,(d<m)%N /\@is_euclidean_analytic_submanifold R n d P) /\
    forall C:set X,@compact E C ->C `<=` U ->
      finite_set (F `&` [set P|exists x,C x /\P x]).
Proof.
move=>X hB hNX T E hU hSU hAnalytic.
case:m=>[|u] hDimension.
- have hRegular:=@federer_3_4_10_zero_regular R n U S hU hSU hAnalytic hDimension.
  exists set0;split.
  + rewrite hRegular;by move=>x [hx hNot].
  split;first by move=>P.
  move=>C hC hCU;rewrite set0I;exact:finite_set0.
- pose L:=@AnalyticRegularLocus.value R n u.+1 U S.
  have hEOpen:@open E U:=(inner_norm_openP hB U).2 hU.
  have hLocal a:U a ->exists W:set E,exists F:set (set E),
      @open E W /\W a /\W `<=` U /\finite_set F /\
      (forall P,F P ->exists d,(d<=u)%N /\@is_euclidean_analytic_submanifold R n d P) /\
      (S `\` L) `&` W `<=` \bigcup_(P in F) P.
    move=>ha.
    have [W [F [hW [hWa [hWU [hFinite [hPieces hCover]]]]]]]:=
      @federer_3_4_10_local_singular_cover R n U S u hU hSU hAnalytic hDimension a ha.
    exists W,F;split;first exact:(inner_norm_openP hB W).2 hW.
    split;first exact:hWa.
    split;first exact:hWU.
    split;first exact:hFinite.
    split;last exact:hCover.
    move=>P hP;have [d [hD hManifold]]:=hPieces P hP.
    exists d;split;last exact:hManifold.
    by move:hD;rewrite ltnS.
  have hAU:(S `\` L) `<=` U by move=>x hx;exact:hSU x hx.1.
  have [F [hCover [hPieces hLocalF]]]:=@euclidean_locally_finite_manifold_cover R n
    U (S `\` L) u hEOpen hAU hLocal.
  exists F;split;first exact:hCover.
  split.
  + move=>P hP;have [d [hD hManifold]]:=hPieces P hP.
    exists d;split;last exact:hManifold.
    by rewrite ltnS.
  + move=>C hC hCU.
    exact:(@locally_finite_family_compact E [the choiceType of set E]
      U F (fun P=>P) C hLocalF hC hCU).
Qed.
