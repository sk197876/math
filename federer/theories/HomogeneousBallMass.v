(** Federer (1969), 3.3.4, p. 291: ball
    mass on T(U) is independent of its centre
    because its invariant measure and transitive
    isometric action are actual. This supporting
    implication uses no density law as a premise. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets functions reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasurePushforward MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [transitive_invariant_closed_ball_mass]:
    the reference-ball mass is independent of z,
    Federer 3.3.4, p. 291. The entire
    actual metric space and all real radii are
    retained, including zero and infinite masses. *)
Theorem transitive_invariant_closed_ball_mass (R:realType) (X:metricType R)
    (G:Type) (A:G->X->X) (mu:set X->\bar R):
  (forall g x y,mdist (A g x) (A g y)=mdist x y) ->
  (forall x y,exists g,A g x=y) ->
  (forall g,measure_pushforward (A g) mu=mu) ->
  forall x y r,mu (metric_closed_ball x r)=mu (metric_closed_ball y r).
Proof.
move=>hIso hTrans hInvariant x y r.
have [g hg]:=hTrans x y.
have hPre:A g @^-1` (metric_closed_ball y r)=metric_closed_ball x r.
  apply/seteqP; split=>z;
    change (is_true (mdist y (A g z)<=r) ->is_true (mdist x z<=r)) ||
    change (is_true (mdist x z<=r) ->is_true (mdist y (A g z)<=r));
    by rewrite -hg hIso.
have h:=congr1 (fun nu=>nu (metric_closed_ball y r)) (hInvariant g).
by rewrite /measure_pushforward hPre in h.
Qed.

(** Source for [transitive_invariant_open_ball_mass]:
    the same centre independence for open balls,
    supporting the I_j inverse-image balls in
    Federer 3.3.4, pp. 291–292. *)
Theorem transitive_invariant_open_ball_mass (R:realType) (X:metricType R)
    (G:Type) (A:G->X->X) (mu:set X->\bar R):
  (forall g x y,mdist (A g x) (A g y)=mdist x y) ->
  (forall x y,exists g,A g x=y) ->
  (forall g,measure_pushforward (A g) mu=mu) ->
  forall x y r,mu [set z|mdist x z<r]=mu [set z|mdist y z<r].
Proof.
move=>hIso hTrans hInvariant x y r.
have [g hg]:=hTrans x y.
have hPre:A g @^-1` [set z|mdist y z<r]=[set z|mdist x z<r].
  apply/seteqP; split=>z;
    change (is_true (mdist y (A g z)<r) ->is_true (mdist x z<r)) ||
    change (is_true (mdist x z<r) ->is_true (mdist y (A g z)<r));
    by rewrite -hg hIso.
have h:=congr1 (fun nu=>nu [set z|mdist y z<r]) (hInvariant g).
by rewrite /measure_pushforward hPre in h.
Qed.
