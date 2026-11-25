(** Federer (1969), 3.4.10, p. 337:
    assemble finite local analytic manifold covers
    into one locally finite family. Reuse
    the selected fivefold and tenfold ball cover
    of 3.1.13, pp. 224-225, and
    restrict each manifold to an open ball. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals topology lra.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness InnerNormTopologyAdapters
  MetricClosedBalls FedererCoverRadius EuclideanPartitionBallCoverUP EuclideanPartitionBallCover
  EuclideanPartitionLocalFiniteness LocallyFiniteFamilyUP FiniteLocallyFiniteRefinement
  AnalyticSubmanifoldUP AnalyticSubmanifoldOpenRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_locally_finite_manifold_cover]: the
    local-to-global covering step of 3.4.10,
    p. 337. Local finiteness follows from
    the already proved tenfold-ball theorem. All
    final pieces are actual analytic manifolds of
    the original local dimensions. *)
Theorem euclidean_locally_finite_manifold_cover (R:realType) n
    (U A:set (R_n R n)) k:
  let hB:=@euclidean_inner_productP R n in
  let E:=inner_metric_space hB in
  @open E U ->A `<=` U ->
  (forall a,U a ->exists W:set E,exists F:set (set E),
    open W /\W a /\W `<=` U /\finite_set F /\
    (forall P,F P ->exists d,(d<=k)%N /\@is_euclidean_analytic_submanifold R n d P) /\
    A `&` W `<=` \bigcup_(P in F) P) ->
  exists F:set (set E),
    A `<=` \bigcup_(P in F) P /\
    (forall P,F P ->exists d,(d<=k)%N /\@is_euclidean_analytic_submanifold R n d P) /\
    @is_locally_finite_family_on E [the choiceType of set E] U F (fun P=>P).
Proof.
move=>hB E hU hAU hLocal.
pose Phi:set (set E):=[set W:set E|open W /\W `<=` U /\
  exists F:set (set E),finite_set F /\
    (forall P,F P ->exists d,(d<=k)%N /\@is_euclidean_analytic_submanifold R n d P) /\
    A `&` W `<=` \bigcup_(P in F) P].
have hPhi W:Phi W ->open W by move=>h;exact:h.1.
have hUnion:(\bigcup_(W in Phi) W)=U.
  apply/seteqP;split.
  - move=>x [W hW hxW];exact:hW.2.1 x hxW.
  - move=>x hx;have [W [F [hW [hxW [hWU hF]]]]]:=hLocal x hx.
    exists W;last exact:hxW.
    split;first exact:hW.
    split;first exact:hWU.
    by exists F.
have [C hC]:=@federer_partition_ball_cover_exists R n Phi hPhi.
pose h:=@federer_cover_radius R E Phi.
pose K:=fun s:E=>metric_closed_ball s (10*h s).
pose B:=fun s:E=>[set x:E|mdist s x<10*h s].
have hPositive s:C s ->0<h s.
  move=>hs;apply:(federer_cover_radius_positive hPhi).
  have [O hO hsO]:=@partition_ball_centers_in_domain R n Phi C hC s hs.
  by exists O;split.
have hEach s:exists P:set (set E),finite_set P /\
    (forall Q,P Q ->exists d,(d<=k)%N /\@is_euclidean_analytic_submanifold R n d Q) /\
    (C s ->A `&` K s `<=` \bigcup_(Q in P) Q).
  case:(pselect (C s))=>hs.
  - have [W [hW hKW]]:=@partition_tenfold_balls_subordinate R n Phi C hC s hs.
    have [P [hFinite [hPieces hCover]]]:=hW.2.2.
    exists P;split;first exact:hFinite.
    split;first exact:hPieces.
    move=>_ x [hxA hxK];apply:hCover;split;first exact:hxA.
    exact:hKW x hxK.
  - exists set0;split;first exact:finite_set0.
    split;first by move=>Q.
    by move=>hImpossible;case:(hs hImpossible).
have [P hP]:=choice hEach.
pose F:=fun s:E=>(fun Q:set E=>Q `&` B s) @` P s.
have hFLocal:@is_locally_finite_family_on E [the choiceType of set E] U
    (\bigcup_(s in C) F s) (fun Q=>Q).
  apply:(@finite_locally_finite_refinement E E U C K F).
  - have hLF:=@partition_tenfold_balls_locally_finite R n Phi C hPhi hC.
    by rewrite hUnion in hLF.
  - move=>s hs;exact:finite_image _ (hP s).1.
  - move=>s hs Q [P0 hP0 <-] x [_ hxB];exact:ltW hxB.
exists (\bigcup_(s in C) F s);split.
- move=>x hxA.
  have hxU:=hAU x hxA.
  have hCover:=partition_fivefold_balls_cover hC.
  rewrite hUnion in hCover.
  have [s hs hxBall]:(\bigcup_(s in C) metric_closed_ball s (5*h s)) x by rewrite hCover.
  have hsPositive:=hPositive s hs.
  have hxB:B s x.
    apply:(le_lt_trans hxBall);change (5*h s<10*h s);lra.
  have hxK:K s x:=ltW hxB.
  have [Q hQ hxQ]:=(hP s).2.2 hs x (conj hxA hxK).
  exists (Q `&` B s);last by split.
  exists s;first exact:hs.
  by exists Q.
split;last exact:hFLocal.
move=>Q [s hs [P0 hP0 <-]].
have [d [hD hManifold]]:=(hP s).2.1 P0 hP0.
exists d;split;first exact:hD.
apply:(@analytic_submanifold_open_restriction R n d P0 (B s) hManifold).
apply:(inner_norm_openP hB (B s)).1.
exact:metric_open_ball_open.
Qed.
