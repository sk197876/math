(** Federer (1969), 3.1.13, p. 224:
    existence of the countable selected ball
    cover with the exact overlap constant
    129^m. The proof uses 2.8.4–2.8.5
    and then 3.1.12 as in the book. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals topology ring lra.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanMetricSeparability
  MetricClosedBalls RealMetricBackground LipschitzUP FedererCoverRadius
  BoundedRadiusFivefoldCover DisjointBallCentersCountable
  LipschitzRadiusOverlap LipschitzRadiusPacking EuclideanPartitionBallCoverUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_partition_ball_cover_exists]:
    all geometric properties of the chosen
    centers on Federer 3.1.13, p. 224,
    before the smooth bumps are defined.
    Empty families, uncountable original families
    and dimension zero are included.
    The containing-ball step uses the erratum,
    p. 4, book p. 224 line 4. *)
Theorem federer_partition_ball_cover_exists (R : realType) m
    (Phi : set (set (inner_metric_space (@euclidean_inner_productP R m)))) :
  (forall T, Phi T -> open T) ->
  exists S, is_federer_partition_ball_cover Phi S.
Proof.
move=>ho.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose U : set X := \bigcup_(T in Phi) T.
pose h := @federer_cover_radius R X Phi.
have hp x : U x -> 0<h x.
  move=>[T hT hx]; apply: (federer_cover_radius_positive ho).
  by exists T.
have hb : exists M : R, forall x, U x -> h x<=M.
  exists (1/20)=>x hx; exact: federer_cover_radius_cap.
have [S [hSU [hdis hcov]]] := bounded_radius_disjoint_fivefold_cover hp hb.
have hcount : countable S.
  apply: (separable_disjoint_ball_centers_countable (euclidean_metric_separable R m) _ hdis).
  move=>s hs; exact: (hp s (hSU s hs)).
have hsub s : S s -> exists T, Phi T /\ metric_closed_ball s (10*h s) `<=` T.
  move=>hs; apply: (federer_cover_radius_subordinate_ball ho).
  have [T hT hx] := hSU s hs; by exists T.
have hcovereq : (\bigcup_(s in S) metric_closed_ball s (5*h s))=U.
  apply/seteqP; split; last exact hcov.
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
have hpacked x (hx : U x) := @federer_3_1_12_indexed R m U S h
  (1/20) 10 10 hSU hp hLip hten hten hsmall hsmall hdis' x hx.
have hlow : (1-(1/20:R)*10)/(1+(1/20)*10)= 1/3 by field.
have hhigh : (1+(1/20:R)*10)/(1-(1/20)*10)=3 by field.
have hfactor : lipschitz_radius_enclosing_factor (1/20:R) 10 10*
    (1+(1/20)*10)/(1-(1/20)*10)= 129.
  by rewrite /lipschitz_radius_enclosing_factor; field.
have hconstant :
    (lipschitz_radius_enclosing_factor (1/20:R) 10 10)^+m*
      (1+(1/20)*10)^+m/(1-(1/20)*10)^+m= 129^+m.
  by rewrite -exprMn -exprVn -exprMn hfactor.
exists S; constructor.
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
