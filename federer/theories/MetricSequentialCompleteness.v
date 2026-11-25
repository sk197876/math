(** General metric topology supporting Federer (1969),
    4.1.24, p. 382: sequential completeness implies the
    original proper-Cauchy-filter completeness. Choose centres
    of filter balls with geometrically shrinking radii,
    use the given sequential limit, and recover the
    entire filter limit. No point or default value is
    chosen in an empty space. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology lra.
From Federer Require Import CompleteMetricUP GeometricUniformTail.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [metric_sequentially_complete_is_complete]: the
    general-topology bridge from actual sequence limits to
    full metric completeness needed in 4.1.24, p. 382.
    This proves the filter conclusion rather than silently
    identifying it with a sequence-only theorem. *)
Theorem metric_sequentially_complete_is_complete (R:realType) (X:metricType R):
  (forall u:nat->X,
    (forall epsilon:R,0<epsilon->exists N,forall i j,
      (N<=i)%N->(N<=j)%N->mdist (u i) (u j)<epsilon)->
    exists x:X,forall epsilon:R,0<epsilon->exists N,forall i,
      (N<=i)%N->mdist x (u i)<epsilon)->
  is_complete_metric_space X.
Proof.
move=>hSequential F hProper hCauchy.
have hFilter:Filter F:=@filter_filter X F hProper.
pose q:R:=1/2.
have hQ:0<q<1 by rewrite /q;apply/andP;split;lra.
have hRadius k:0<q^+k:=exprn_gt0 k (andP hQ).1.
have hCentres k:exists x:X,F (ball x (q^+k)).
  exact:((@cauchyP R X F hProper).1 hCauchy (q^+k) (hRadius k)).
have[c hC]:=choice hCentres.
have hSequence:forall epsilon:R,0<epsilon->exists N,forall i j,
    (N<=i)%N->(N<=j)%N->mdist (c i) (c j)<epsilon.
  move=>epsilon hEpsilon.
  have hHalf:0<epsilon/2 by rewrite divr_gt0 //;lra.
  have[N hN]:=@geometric_uniform_tail R q 1 (epsilon/2) hQ (ler01) hHalf.
  exists N=>i j hNi hNj.
  have[z [hzi hzj]]:=@filter_ex X F hProper _
    (@filterI X F hFilter _ _ (hC i) (hC j)).
  rewrite !ballEmdist in hzi hzj.
  have hDistanceI:mdist (c i) z<q^+i:=hzi.
  have hDistanceJ:mdist (c j) z<q^+j:=hzj.
  have hi:=hN i hNi;have hj:=hN j hNj.
  rewrite !mulr1 in hi hj.
  have hNearI:mdist (c i) z<epsilon/2:=lt_trans hDistanceI hi.
  have hNearJ:mdist (c j) z<epsilon/2:=lt_trans hDistanceJ hj.
  have hTriangle:=metric_triangle (c i) z (c j).
  rewrite (metric_sym z (c j)) in hTriangle.
  apply:le_lt_trans hTriangle _.
  have hSum:=ltrD hNearI hNearJ;by rewrite -splitr in hSum.
have[x hLimit]:=hSequential c hSequence.
exists x=>A hA.
have[epsilon hEpsilon hBall]:=(metricType_numDomainType.nbhs_mdistP x A).1 hA.
have hHalf:0<epsilon/2 by rewrite divr_gt0 //;lra.
have[N hN]:=hLimit (epsilon/2) hHalf.
have[M hM]:=@geometric_uniform_tail R q 1 (epsilon/2) hQ (ler01) hHalf.
pose k:=maxn N M.
have hNear:=hN k (leq_maxl N M).
have hSmall:=hM k (leq_maxr N M);rewrite mulr1 in hSmall.
apply:(@filterS X F hFilter _ _ _ (hC k))=>y hy.
apply:hBall.
rewrite ballEmdist in hy.
have hDistanceY:mdist (c k) y<q^+k:=hy.
have hSmallY:mdist (c k) y<epsilon/2:=lt_trans hDistanceY hSmall.
have hTriangle:=metric_triangle x (c k) y.
apply:le_lt_trans hTriangle _.
have hSum:=ltrD hNear hSmallY;by rewrite -splitr in hSum.
Qed.
