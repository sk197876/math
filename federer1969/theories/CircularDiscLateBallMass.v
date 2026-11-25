(** Federer (1969), 3.3.19, p. 306: remove
    the parent-scale error by the original first split
    and actual small-ball tangential packing. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric MetricClosedBalls FactorialDiscScalesSealed
  CircularDiscRefinement CircularDiscTreeUP CircularDiscLimitUP CircularDiscHitCount CircularDiscFirstSplitUP
  CircularDiscBallFirstSplit CircularDiscBallFirstParent CircularDiscSmallBallTangentSpacing CircularDiscTangentialBallMass
  CircularDiscApproximateBallMass FiniteCellHitMeasureUP FiniteCellHitIndicesLaws
  HausdorffMeasure MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Mass.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation N:=(inner_norm (@euclidean_inner_productP R 2)).
Local Notation B:=(@euclidean_inner_product R 2).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation mu:=(@hausdorff_measure R [the metricType R of E] 1).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable A:set E.
Hypothesis hA:is_circular_disc_limit H A.

(** Source for [circular_disc_uniform_late_ball_mass]: for
    every positive epsilon there is a positive real
    cutoff such that EVERY original a in A and
    EVERY positive smaller radius t satisfy
    H1(A intersect B(a,t))<=(1+epsilon)t. Actual first
    splitting parents, original translated child pieces,
    strict tangent packing and uniform cap approximation
    discharge all scales. This proves the needed mass
    estimate in the last assertion of 3.3.19, p. 306. *)
Theorem circular_disc_uniform_late_ball_mass (eps:R):0<eps ->exists delta:R,0<delta /\
  forall (a:E) (t:R),A a ->0<t ->t<delta ->
  (mu (A `&` metric_closed_ball a t)<=((1+eps)* t)%:E)%E.
Proof.
move=>hEps.
have [q [J1 [hq hSpacing]]]:= @circular_disc_small_ball_tangent_spacing R H hH A hA.
have hb:0<eps* q by rewrite mulr_gt0.
have [J2 hApprox]:= @circular_disc_approximate_parent_ball_mass R H hH A hA (eps* q) hb.
pose J:= maxn J1 J2.
have [delta [hDelta hLate]]:= @circular_disc_small_balls_split_late R H hH J.
exists delta;split=>// a t ha ht htSmall.
have [j hFirst]:= @circular_disc_positive_ball_first_split R H hH A hA a t ha ht.
have hj:= hLate a t j ht htSmall hFirst.
have hj1:(J1<=j)%N:= leq_trans (leq_maxl J1 J2) hj.
have hj2:(J2<=j)%N:= leq_trans (leq_maxr J1 J2) hj.
have ht0:0<=t:= ltW ht.
have [z [hz [haParent [hParentCover hChildren]]]]:= @circular_disc_ball_first_parent R H hH A hA j a t ha ht0 hFirst.
pose T:= metric_closed_ball a t.
pose F:= @circular_disc_hit_indices R H j.+1 T.
case:(ltP t (q* rho j))=>[hSmall|hLarge].
- have [e [he hGrid]]:= hSpacing j z a t hj1 hz ha haParent ht0 hSmall.
  have hFSubset:(F `<=` H j.+1)%fset:= @finite_cell_hit_indices_subset E E (H j.+1)
    (fun c=>metric_closed_ball c (rho j.+1)) T.
  have hFCount:(2<=#|` F|)%N:= hFirst.1.
  have hSelf:T a by change (is_true (mdist a a<=t));by rewrite mdistxx.
  have [c0 [hc0 haC0]]:=(hA a).1 ha j.+1.
  have hc0Hit:c0 \in F.
    apply/(@finite_cell_hit_indices_membership E E (H j.+1)
      (fun c=>metric_closed_ball c (rho j.+1)) T c0).
    split=>//;by exists a;split.
  have hOwn:exists c:E,c \in F /\metric_closed_ball c (rho j.+1) a by exists c0.
  have hMeeting c:c \in F ->(metric_closed_ball c (rho j.+1) `&` T)!=set0.
    move=>hc.
    have [_ [x [hxC hxT]]]:=(@finite_cell_hit_indices_membership E E (H j.+1)
      (fun c=>metric_closed_ball c (rho j.+1)) T c).1 hc.
    by exists x;split.
  have hNear c:c \in F ->mdist c a<=t+rho j.+1.
    move=>hc.
    have [x [hxC hxT]]:= hMeeting c hc.
    have hTriangle:= metric_triangle c x a.
    have hx1:mdist c x<=rho j.+1:= hxC.
    have hx2:mdist x a<=t by rewrite metric_sym;exact:hxT.
    lra.
  have hStrict c d:c \in F ->d \in F ->c!=d ->6* rho j.+1<`|B (c-d) e|.
    move=>hc hd hDifferent.
    have [k hC]:= hChildren c hc.
    have [l hD]:= hChildren d hd.
    have hKL:k!=l.
      apply/eqP=>hEqual;move:hDifferent;by rewrite hC hD hEqual eqxx.
    have hHitK:(metric_closed_ball (circular_disc_child_center z (rho j) k) (rho j.+1) `&` T)!=set0.
      by rewrite -hC;exact:hMeeting c hc.
    have hHitL:(metric_closed_ball (circular_disc_child_center z (rho j) l) (rho j.+1) `&` T)!=set0.
      by rewrite -hD;exact:hMeeting d hd.
    rewrite hC hD;exact:hGrid k l hKL hHitK hHitL.
  have hFineCover:(A `&` T) `<=` A `&` (\bigcup_(c in [set` F]) metric_closed_ball c (rho j.+1)).
    move=>x [hxA hxT];split=>//.
    have [c [hc hxC]]:=(hA x).1 hxA j.+1.
    have hcHit:c \in F.
      apply/(@finite_cell_hit_indices_membership E E (H j.+1)
        (fun c=>metric_closed_ball c (rho j.+1)) T c).
      split=>//;by exists x;split.
    by exists c.
  have hMass:= @circular_disc_tangential_ball_mass R H hH A hA j.+1 F a e t
    hFSubset hFCount ht0 he hOwn hNear hStrict hFineCover.
  have hScalar:t<=(1+eps)* t by have h:= mulr_ge0 (ltW hEps) ht0;nra.
  exact:(le_trans hMass (lee_tofin hScalar)).
- have hEqual:(A `&` T)=(A `&` metric_closed_ball z (rho j)) `&` T.
    apply/seteqP;split.
    + move=>x hx;split;first exact:hParentCover x hx.
      exact:hx.2.
    + by move=>x [[hxA _] hxT];split.
  have hBound:= hApprox j z a t hj2 hz ha haParent ht0.
  have hProduct:= ler_wpM2l (ltW hEps) hLarge.
  have hScalar:t+(eps* q)* rho j<=(1+eps)* t by nra.
  rewrite hEqual;exact:(le_trans hBound (lee_tofin hScalar)).
Qed.
End Mass.
