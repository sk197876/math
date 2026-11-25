(** Federer (1969), 3.1.12, pp. 223–224:
    the theorem with the printed disjoint family of balls.
    Indexing this family by centers adds no assumption. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals topology.
From Federer Require Import EuclideanInnerProduct InnerMetric RealMetricBackground
  LipschitzUP LipschitzConstant MetricClosedBalls CountablyClosedFamilyUP InnerClosedBallCenters
  LipschitzRadiusOverlap LipschitzRadiusPacking.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_1_12_bound]: both conclusions of
    Federer 3.1.12, pp. 223–224, from the disjointness
    of the set family {B[s,h(s)]:s in S}. Unique centers
    of nonempty Euclidean balls justify the indexed formulation.
    The containing-ball argument uses the erratum, p. 4,
    book p. 224 line 4. *)
Theorem federer_3_1_12_bound (R : realType) m
    (U S : set (inner_metric_space (@euclidean_inner_productP R m)))
    (h : inner_metric_space (@euclidean_inner_productP R m)->R)
    (lambda alpha beta : R) x :
  S `<=` U -> (forall y, U y -> 0<h y) ->
  is_metric_lipschitz_bound U (fun y=>(h y : real_line_metric R)) lambda ->
  0<alpha -> 0<beta -> lambda*alpha<1 -> lambda*beta<1 ->
  set_family_disjoint [set T | exists s, S s /\ T=metric_closed_ball s (h s)] ->
  U x ->
  (forall s, lipschitz_radius_overlap S h alpha beta x s ->
    (1-lambda*beta)/(1+lambda*alpha)<=h x/h s /\
      h x/h s<=(1+lambda*beta)/(1-lambda*alpha)) /\
  finite_set (lipschitz_radius_overlap S h alpha beta x) /\
  ((#|` fset_set (lipschitz_radius_overlap S h alpha beta x)|)%:R : R)<=
    (lipschitz_radius_enclosing_factor lambda alpha beta)^+m*
      (1+lambda*beta)^+m/(1-lambda*alpha)^+m.
Proof.
move=>hSU hp hLip ha hb hla hlb hfamily hx.
have hdis s t : S s -> S t -> s!=t -> forall y,
    metric_closed_ball s (h s) y -> metric_closed_ball t (h t) y -> False.
  move=>hs ht hne y hy hz.
  have hbs : [set T | exists u, S u /\ T=metric_closed_ball u (h u)]
      (metric_closed_ball s (h s)) by exists s.
  have hbt : [set T | exists u, S u /\ T=metric_closed_ball u (h u)]
      (metric_closed_ball t (h t)) by exists t.
  have hneq : metric_closed_ball s (h s)<>metric_closed_ball t (h t).
    move=>he; have hst := inner_closed_ball_center_unique
      (ltW (hp s (hSU s hs))) (ltW (hp t (hSU t ht))) he.
    by move:hne; rewrite hst eqxx.
  have he := hfamily _ _ hbs hbt hneq.
  have hh : (metric_closed_ball s (h s) `&` metric_closed_ball t (h t)) y := conj hy hz.
  by rewrite he in hh.
exact (@federer_3_1_12_indexed R m U S h lambda alpha beta
  hSU hp hLip ha hb hla hlb hdis x hx).
Qed.

(** Source for [federer_3_1_12]: Federer 3.1.12, pp. 223–224,
    with the printed Lipschitzian hypothesis and lambda >= Lip(h).
    The sealed least-constant laws yield the distance bound used above;
    both radius ratios and the cardinal estimate follow without
    assuming finiteness or countability of the original ball family. *)
Theorem federer_3_1_12 (R : realType) m
    (U S : set (inner_metric_space (@euclidean_inner_productP R m)))
    (h : inner_metric_space (@euclidean_inner_productP R m)->R)
    (h_lipschitz : is_metric_lipschitz U (fun y=>(h y : real_line_metric R)))
    (lambda alpha beta : R) x :
  S `<=` U -> (forall y, U y -> 0<h y) ->
  metric_lipschitz_constant h_lipschitz<=lambda ->
  0<alpha -> 0<beta -> lambda*alpha<1 -> lambda*beta<1 ->
  set_family_disjoint [set T | exists s, S s /\ T=metric_closed_ball s (h s)] ->
  U x ->
  (forall s, lipschitz_radius_overlap S h alpha beta x s ->
    (1-lambda*beta)/(1+lambda*alpha)<=h x/h s /\
      h x/h s<=(1+lambda*beta)/(1-lambda*alpha)) /\
  finite_set (lipschitz_radius_overlap S h alpha beta x) /\
  ((#|` fset_set (lipschitz_radius_overlap S h alpha beta x)|)%:R : R)<=
    (lipschitz_radius_enclosing_factor lambda alpha beta)^+m*
      (1+lambda*beta)^+m/(1-lambda*alpha)^+m.
Proof.
move=>hSU hp hLambda ha hb hla hlb hfamily hx.
have hbound : is_metric_lipschitz_bound U
    (fun y=>(h y : real_line_metric R)) lambda.
  split; first exact (le_trans (metric_lipschitz_constant_nonnegative h_lipschitz) hLambda).
  move=>y z hy hz.
  exact (le_trans (metric_lipschitz_constant_attained h_lipschitz hy hz)
    (ler_wpM2r (mdist_ge0 y z) hLambda)).
exact (@federer_3_1_12_bound R m U S h lambda alpha beta x
  hSU hp hbound ha hb hla hlb hfamily hx).
Qed.
