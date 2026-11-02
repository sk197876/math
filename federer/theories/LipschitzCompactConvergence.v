(** Federer (1969), 2.10.21, p. 182: pointwise convergence in E_s is
    equivalent to uniform convergence on each compact subset. The finite-net
    estimate is the printed two-Lipschitz-error bound. Use arbitrary
    filters, so sequences are not silently substituted for convergence in
    the cartesian product topology. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology lra.
From Federer Require Import LipschitzUP MetricClosedBalls CompactFiniteCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lipschitz_finite_net_estimate]: direct
    estimate on p. 182 in 2.10.21, expressed as
    an arbitrary upper bound rather than an attained
    supremum. The estimate also holds for infinite nets. *)
Lemma lipschitz_finite_net_estimate (R : realType) (X Y : metricType R)
    (f g : X -> Y) (s delta t : R) (Z A : set X) :
  is_metric_lipschitz_bound setT f s -> is_metric_lipschitz_bound setT g s ->
  A `<=` \bigcup_(z in Z) metric_closed_ball z delta ->
  (forall z, Z z -> mdist (f z) (g z)<=t) ->
  forall x, A x -> mdist (f x) (g x)<=2*s*delta+t.
Proof.
move=> [hs hf] [_ hg] hcover hZ x hx.
have [z hz hzx] := hcover x hx.
have h1 := metric_triangle (f x) (f z) (g x).
have h2 := metric_triangle (f z) (g z) (g x).
have hfx := hf x z I I; have hgx := hg z x I I.
rewrite (metric_sym x z) in hfx.
have hmult := ler_wpM2l hs hzx.
have hpoint := hZ z hz; lra.
Qed.

(** Source for [metric_functions_pointwise_converge]: the
    pointwise convergence used for E_s in 2.10.21,
    p. 182. Eventual metric inequalities describe
    arbitrary filters, including nets. *)
Definition metric_functions_pointwise_converge (R : realType) (I : Type)
    (X : Type) (Y : metricType R) (F : set_system I) (u : I -> X -> Y) (f : X -> Y) :=
  forall x e, (0<e)%R -> F [set i | mdist (f x) (u i x)<e].

(** Source for [metric_functions_compact_uniformly_converge]: the
    compact uniform convergence used in 2.10.21,
    p. 182. The eventual index is independent of
    the point in the chosen compact subset. *)
Definition metric_functions_compact_uniformly_converge (R : realType) (I : Type)
    (X : topologicalType) (Y : metricType R) (F : set_system I) (u : I -> X -> Y) (f : X -> Y) :=
  forall K, compact K -> forall e, (0<e)%R ->
    F [set i | forall x, K x -> mdist (f x) (u i x)<e].

(** Source for [lipschitz_pointwise_compact_uniform]: direct
    convergence equivalence of 2.10.21, p. 182.
    Every approximant and the limit belong to E_s;
    arbitrary compact sets, including the empty set, are allowed. *)
Theorem lipschitz_pointwise_compact_uniform (R : realType) (I : Type)
    (X Y : metricType R) (F : set_system I) (FF : Filter F)
    (u : I -> X -> Y) (f : X -> Y) (s : R) :
  is_metric_lipschitz_bound setT f s ->
  (forall i, is_metric_lipschitz_bound setT (u i) s) ->
  (metric_functions_pointwise_converge F u f <->
   metric_functions_compact_uniformly_converge F u f).
Proof.
move=> hf hu; split.
- move=> hp K hK e he.
  have hs := hf.1.
  have hsp : 0<s+1 by lra.
  pose d := e/(4*(s+1)).
  have hd : 0<d by rewrite /d divr_gt0 // mulr_gt0 // ltr0n.
  have h4 : (0<4 :> R) by rewrite ltr0n.
  have hden : 4*(s+1)!=0 by rewrite (gt_eqF (mulr_gt0 h4 hsp)).
  have hde : (4*(s+1))*d=e by rewrite mulrC /d divfK.
  have hss : s<=s+1 by lra.
  have hmul := ler_wpM2r (ltW hd) hss.
  have hcover : K `<=` \bigcup_(z in K) [set x | mdist z x<d].
    move=> x hx; exists x=> //; by rewrite /= mdistxx.
  have [Z hZ hcov] := @compact_open_finite_cover X X K (fun z => [set x | mdist z x<d]) K
    hK (fun z _ => metric_open_ball_open z d) hcover.
  have hnear : F (\bigcap_(z in [set` Z]) [set i | mdist (f z) (u i z)<e/2]).
    apply: (@filter_bigI I X Z _ F FF)=> z hz; apply: hp; by rewrite divr_gt0 // ltr0n.
  apply: (@filterS I F FF _ _ _ hnear)=> i hi x hx.
  have [z hz hzx] := hcov x hx.
  have hdist := ltW hzx.
  have hpoint : mdist (f z) (u i z)<e/2 := hi z hz.
  have h1 := metric_triangle (f x) (f z) (u i x).
  have h2 := metric_triangle (f z) (u i z) (u i x).
  have hfx := hf.2 x z Logic.I Logic.I; have hux := (hu i).2 z x Logic.I Logic.I.
  rewrite (metric_sym x z) in hfx.
  have hmult := ler_wpM2l hs hdist.
  lra.
- move=> hc x e he.
  have hh := hc [set x] (@compact_set1 X x) e he.
  apply: (@filterS I F FF _ _ _ hh)=> i hi; exact: hi x erefl.
Qed.

(** Source for [lipschitz_compact_uniform_neighborhood]: supporting
    neighbourhood form of the convergence assertion in
    2.10.21, p. 182. Finitely many coordinate
    constraints control the uniform distance on a
    compact set, relative to E_s. *)
Theorem lipschitz_compact_uniform_neighborhood (R : realType) (X Y : metricType R)
    (f : prod_topology (fun _ : X => Y)) (s : R) (K : set X) (e : R) :
  is_metric_lipschitz_bound setT f s -> compact K -> 0<e ->
  exists U, nbhs f U /\ forall g, U g -> is_metric_lipschitz_bound setT g s ->
    forall x, K x -> mdist (f x) (g x)<e.
Proof.
move=> hf hK he.
have hs := hf.1.
have hsp : 0<s+1 by lra.
pose d := e/(4*(s+1)).
have hd : 0<d by rewrite /d divr_gt0 // mulr_gt0 // ltr0n.
have h4 : (0<4 :> R) by rewrite ltr0n.
have hden : 4*(s+1)!=0 by rewrite (gt_eqF (mulr_gt0 h4 hsp)).
have hde : (4*(s+1))*d=e by rewrite mulrC /d divfK.
have hss : s<=s+1 by lra.
have hmul := ler_wpM2r (ltW hd) hss.
have hcover : K `<=` \bigcup_(z in K) [set x | mdist z x<d].
  move=> x hx; exists x=> //; by rewrite /= mdistxx.
have [Z hZ hcov] := @compact_open_finite_cover X X K (fun z => [set x | mdist z x<d]) K
  hK (fun z _ => metric_open_ball_open z d) hcover.
pose U : set (prod_topology (fun _ : X => Y)) :=
  \bigcap_(z in [set` Z]) [set g | mdist (f z) (g z)<e/2].
have hcoords z (hz : z \in Z) : nbhs f
    [set g : prod_topology (fun _ : X => Y) | mdist (f z) (g z)<e/2].
  have he2 : 0<e/2 by rewrite divr_gt0 // ltr0n.
  have hp : nbhs f ((fun g : prod_topology (fun _ : X => Y) => g z) @^-1` ball (f z) (e/2)).
    exact: (@proj_continuous X (fun _ : X => Y) z f _ (nbhsx_ballx (f z) (e/2) he2)).
  by rewrite ballEmdist in hp.
have hnear : nbhs f U := @filter_bigI (prod_topology (fun _ : X => Y)) X Z
  (fun z => [set g : prod_topology (fun _ : X => Y) | mdist (f z) (g z)<e/2])
  (nbhs f) (nbhs_filter f) hcoords.
exists U; split=> // g hg hLip x hx.
have [z hz hzx] := hcov x hx.
have hdist := ltW hzx.
have hpoint : mdist (f z) (g z)<e/2 := hg z hz.
have h1 := metric_triangle (f x) (f z) (g x).
have h2 := metric_triangle (f z) (g z) (g x).
have hfx := hf.2 x z I I; have hgx := hLip.2 z x I I.
rewrite (metric_sym x z) in hfx.
have hmult := ler_wpM2l hs hdist.
lra.
Qed.
