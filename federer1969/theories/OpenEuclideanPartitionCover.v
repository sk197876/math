(** Federer (1969), 3.1.20, p. 232: selected closed balls P_i
    have the locally finite bounds of 3.1.13, and their open
    inner balls Q_i cover the coordinate-neighbourhood union. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals topology ring lra.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanMetricSeparability
  MetricClosedBalls RealMetricBackground LipschitzUP FedererCoverRadius
  EuclideanOpenFivefoldCover DisjointBallCentersCountable
  LipschitzRadiusOverlap LipschitzRadiusPacking EuclideanPartitionBallCoverUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [open_federer_partition_ball_cover_exists]: the
    open Q_i cover used in Federer 3.1.20, p. 232, together
    with all geometric selection laws of 3.1.13, pp. 224–225.
    This positive-dimensional support lemma retains the exact
    overlap bound 129^(n+1) and the same fivefold and tenfold radii. *)
Theorem open_federer_partition_ball_cover_exists (R:realType) n
    (Phi:set (set (inner_metric_space (@euclidean_inner_productP R n.+1)))) :
  (forall T,Phi T -> open T) -> exists S,
    is_federer_partition_ball_cover Phi S /\
    (\bigcup_(T in Phi) T) `<=` \bigcup_(s in S)
      [set x|mdist s x<5*federer_cover_radius Phi s].
Proof.
move=>ho.
pose X := inner_metric_space (@euclidean_inner_productP R n.+1).
pose U : set X := \bigcup_(T in Phi) T.
pose h := @federer_cover_radius R X Phi.
have hp x : U x -> 0<h x.
  move=>[T hT hx]; apply: (federer_cover_radius_positive ho).
  by exists T.
have hb : exists M : R, forall x, U x -> h x<=M.
  exists (1/20)=>x hx; exact: federer_cover_radius_cap.
have [S [hSU [hdis hcov]]] := euclidean_positive_radius_open_fivefold_cover hp hb.
have hcount : countable S.
  apply: (separable_disjoint_ball_centers_countable (euclidean_metric_separable R n.+1) _ hdis).
  move=>s hs; exact: (hp s (hSU s hs)).
have hsub s : S s -> exists T, Phi T /\ metric_closed_ball s (10*h s) `<=` T.
  move=>hs; apply: (federer_cover_radius_subordinate_ball ho).
  have [T hT hx] := hSU s hs; by exists T.
have hcovereq : (\bigcup_(s in S) metric_closed_ball s (5*h s))=U.
  apply/seteqP; split.
  2: { move=>x hx; have [s hs hxs]:=hcov x hx.
       exists s=>//; exact: ltW hxs. }
  move=>x [s hs hxs]; have [T [hT hBT]] := hsub s hs.
  exists T=> //; apply: hBT.
  change (is_true (mdist s x<=10*h s)).
  have hsp := ltW (hp s (hSU s hs)).
  apply: (le_trans hxs); lra.
have hLip : is_metric_lipschitz_bound U (fun x=>(h x : real_line_metric R)) (1/20).
  split; first by rewrite divr_ge0 // ler0n.
  move=>x y hx hy; rewrite real_line_metric_distanceE.
  exact: federer_cover_radius_lipschitz.
have hten : (0:R)<10 by rewrite ltr0n.
have hsmall : (1/20:R)*10<1 by lra.
have hdis' s t : S s -> S t -> s!=t -> forall y,
    metric_closed_ball s (h s) y -> metric_closed_ball t (h t) y -> False.
  move=>hs ht hne y hys hyt.
  have hn : s<>t by move=>he; move: hne; by rewrite he eqxx.
  have hh : (metric_closed_ball s (h s) `&` metric_closed_ball t (h t)) y by split.
  by rewrite (hdis s t hs ht hn) in hh.
have hpacked x (hx : U x) := @federer_3_1_12_indexed R n.+1 U S h
  (1/20) 10 10 hSU hp hLip hten hten hsmall hsmall hdis' x hx.
have hlow : (1-(1/20:R)*10)/(1+(1/20)*10)= 1/3 by field.
have hhigh : (1+(1/20:R)*10)/(1-(1/20)*10)=3 by field.
have hfactor : lipschitz_radius_enclosing_factor (1/20:R) 10 10*
    (1+(1/20)*10)/(1-(1/20)*10)= 129.
  by rewrite /lipschitz_radius_enclosing_factor; field.
have hconstant :
    (lipschitz_radius_enclosing_factor (1/20:R) 10 10)^+n.+1*
      (1+(1/20)*10)^+n.+1/(1-(1/20)*10)^+n.+1= 129^+n.+1.
  by rewrite -exprMn -exprVn -exprMn hfactor.
exists S; split; last exact hcov.
constructor.
- exact hSU.
- exact hcount.
- exact hdis.
- exact hcovereq.
- exact hsub.
- move=>x hx; exact: (hpacked x hx).2.1.
- move=>x hx; have hh := (hpacked x hx).2.2.
  by rewrite hconstant in hh.
- move=>x hx s hs; have [hl hu] := (hpacked x hx).1 s hs.
  rewrite hlow in hl; rewrite hhigh in hu.
  by apply/andP; split.
Qed.
