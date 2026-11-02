(** Federer (1969), 3.1.12, pp. 223–224:
    comparison of a positive Lipschitz radius function at
    centers whose enlarged balls intersect. The geometric
    comparison works in any metric space. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology lra.
From Federer Require Import LipschitzUP RealMetricBackground MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lipschitz_radius_overlap]: the family S_x
    in Federer 3.1.12, p. 223, consists of
    centers whose beta-enlarged balls meet the alpha-enlarged
    ball at x. Both balls are closed, as printed. *)
Definition lipschitz_radius_overlap (R : realType) (X : metricType R)
    (S : set X) (h : X->R) (alpha beta : R) (x : X) : set X :=
  S `&` [set s | exists z,
    metric_closed_ball x (alpha*h x) z /\
    metric_closed_ball s (beta*h s) z].

(** Source for [positive_lipschitz_radius_ratios]:
    the two scalar rearrangements in the proof of
    Federer 3.1.12, p. 224. Positivity of
    the denominators follows from the printed smallness conditions. *)
Lemma positive_lipschitz_radius_ratios (R : realType) (r s lambda alpha beta : R) :
  0<r -> 0<s -> 0<=lambda -> 0<alpha -> 0<beta ->
  lambda*alpha<1 -> lambda*beta<1 ->
  `|r-s|<=lambda*(alpha*r+beta*s) ->
  (1-lambda*beta)/(1+lambda*alpha)<=r/s /\
    r/s<=(1+lambda*beta)/(1-lambda*alpha).
Proof.
move=> hr hs hl ha hb hla hlb hnorm.
have hlo : r-s<=lambda*(alpha*r+beta*s).
  exact: le_trans (ler_norm _) hnorm.
have hhi : s-r<=lambda*(alpha*r+beta*s).
  apply: le_trans (ler_norm _) _; by rewrite -opprB normrN.
have hD : 0<1+lambda*alpha by have := mulr_ge0 hl (ltW ha); lra.
have hE : 0<1-lambda*alpha by lra.
split.
- rewrite (@ler_pdivlMr R s _ _ hs) mulrAC (@ler_pdivrMr R (1+lambda*alpha) _ _ hD); nra.
- rewrite (@ler_pdivrMr R s _ _ hs) mulrAC (@ler_pdivlMr R (1-lambda*alpha) _ _ hE); nra.
Qed.

(** Source for [lipschitz_radius_overlap_distance]:
    the triangle inequality |x-s|<=alpha h(x)+beta h(s)
    in Federer 3.1.12, p. 224. *)
Lemma lipschitz_radius_overlap_distance (R : realType) (X : metricType R)
    (S : set X) (h : X->R) (alpha beta : R) (x s : X) :
  lipschitz_radius_overlap S h alpha beta x s ->
  mdist x s<=alpha*h x+beta*h s.
Proof.
move=> [_ [z [hxz hsz]]].
have hh := metric_triangle x z s.
rewrite (metric_sym z s) in hh.
exact: le_trans hh (lerD hxz hsz).
Qed.

(** Source for [lipschitz_radius_overlap_ratios]:
    the displayed comparison of h(x)/h(s) in
    Federer 3.1.12, p. 223, proved on p. 224. *)
Theorem lipschitz_radius_overlap_ratios (R : realType) (X : metricType R)
    (U S : set X) (h : X->R) (lambda alpha beta : R) (x s : X) :
  S `<=` U -> (forall y, U y -> 0<h y) ->
  is_metric_lipschitz_bound U (fun y=>(h y : real_line_metric R)) lambda ->
  0<alpha -> 0<beta -> lambda*alpha<1 -> lambda*beta<1 ->
  U x -> lipschitz_radius_overlap S h alpha beta x s ->
  (1-lambda*beta)/(1+lambda*alpha)<=h x/h s /\
    h x/h s<=(1+lambda*beta)/(1-lambda*alpha).
Proof.
move=> hSU hp [hl hLip] ha hb hla hlb hx hs.
have hsU := hSU s hs.1.
apply: (@positive_lipschitz_radius_ratios R (h x) (h s) lambda alpha beta
  (hp x hx) (hp s hsU) hl ha hb hla hlb).
have hh := hLip x s hx hsU.
rewrite real_line_metric_distanceE in hh.
exact (le_trans hh (ler_wpM2l hl (lipschitz_radius_overlap_distance hs))).
Qed.

(** Source for [lipschitz_radius_overlap_radius_bounds]:
    the equivalent lower and upper bounds on h(s)
    used in the packing estimate of Federer 3.1.12,
    p. 224. These are derived from the same
    inequalities, not added as radius hypotheses. *)
Theorem lipschitz_radius_overlap_radius_bounds (R : realType) (X : metricType R)
    (U S : set X) (h : X->R) (lambda alpha beta : R) (x s : X) :
  S `<=` U -> (forall y, U y -> 0<h y) ->
  is_metric_lipschitz_bound U (fun y=>(h y : real_line_metric R)) lambda ->
  0<alpha -> 0<beta -> lambda*alpha<1 -> lambda*beta<1 ->
  U x -> lipschitz_radius_overlap S h alpha beta x s ->
  ((1-lambda*alpha)/(1+lambda*beta))*h x<=h s /\
    h s<=((1+lambda*alpha)/(1-lambda*beta))*h x.
Proof.
move=> hSU hp hLip ha hb hla hlb hx hs.
have hsU := hSU s hs.1.
have hdist := lipschitz_radius_overlap_distance hs.
have hnorm : `|h s-h x|<=lambda*(beta*h s+alpha*h x).
  have hh := hLip.2 s x hsU hx.
  rewrite real_line_metric_distanceE metric_sym in hh.
  have hmult := ler_wpM2l hLip.1 hdist.
  rewrite addrC in hmult; exact (le_trans hh hmult).
have [hl hu] := @positive_lipschitz_radius_ratios R (h s) (h x) lambda beta alpha
  (hp s hsU) (hp x hx) hLip.1 hb ha hlb hla hnorm.
split.
- by move: hl; rewrite (@ler_pdivlMr R (h x) _ _ (hp x hx)).
- by move: hu; rewrite (@ler_pdivrMr R (h x) _ _ (hp x hx)).
Qed.

(** Source for [lipschitz_radius_enclosing_factor]: the
    coefficient gamma in Federer 3.1.12, p. 224. *)
Definition lipschitz_radius_enclosing_factor (R : realType)
    (lambda alpha beta : R) : R :=
  alpha+(beta+1)*(1+lambda*alpha)/(1-lambda*beta).

(** Source for [lipschitz_radius_overlap_ball_inclusion]:
    B[s,h(s)] lies in B[x,gamma h(x)], Federer
    3.1.12, p. 224. The intermediate expression
    uses alpha h(x)+(beta+1)h(s), following the correction
    in erratum p. 4, book p. 224 line 4. *)
Theorem lipschitz_radius_overlap_ball_inclusion (R : realType) (X : metricType R)
    (U S : set X) (h : X->R) (lambda alpha beta : R) (x s : X) :
  S `<=` U -> (forall y, U y -> 0<h y) ->
  is_metric_lipschitz_bound U (fun y=>(h y : real_line_metric R)) lambda ->
  0<alpha -> 0<beta -> lambda*alpha<1 -> lambda*beta<1 ->
  U x -> lipschitz_radius_overlap S h alpha beta x s ->
  metric_closed_ball s (h s) `<=`
    metric_closed_ball x (lipschitz_radius_enclosing_factor lambda alpha beta*h x).
Proof.
move=> hSU hp hLip ha hb hla hlb hx hs y hy.
have [hl hu] := lipschitz_radius_overlap_radius_bounds hSU hp hLip ha hb hla hlb hx hs.
have hd := lipschitz_radius_overlap_distance hs.
have hdist := le_trans (metric_triangle x s y) (lerD hd hy).
have hb1 : 0<=beta+1 by lra.
have hscale := ler_wpM2l hb1 hu.
change (is_true (mdist x y<=lipschitz_radius_enclosing_factor lambda alpha beta*h x)).
rewrite /lipschitz_radius_enclosing_factor.
nra.
Qed.
