(** Federer (1969), 4.1.2, p. 347: pointwise positive-parameter
    convergence is convergence in the original weak dual topology.
    This adapter uses the proved arbitrary-filter characterization. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormOpenTopology OpenFamilyConvergence
  WeakEvaluationConvergenceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weak_positive_parameter_limit]: the positive-epsilon
    weak convergence assertion in Federer 4.1.2, p. 347.
    Every original weak open neighbourhood is eventually attained;
    no sequential or weaker topology is substituted. *)
Theorem weak_positive_parameter_limit (R:realType) (E D:choiceType)
    (ev:D->E->R) (O:set (set D)) (hO:is_weak_evaluation_convergence ev O)
    (a:R->D) (d:D):
  (forall f eta,0<eta ->exists r:R,0<r /\ forall e:R,0<e ->e<r ->
    `|ev (a e) f-ev d f|<eta) ->
  forall V,O V ->V d ->exists r:R,0<r /\ forall e:R,0<e ->e<r ->V (a e).
Proof.
move=>hPoint.
pose F:set_system R:=fun A=>exists r:R,0<r /\ forall e:R,0<e ->e<r ->A e.
have hF:Filter F.
  constructor.
  - exists 1; split; first exact:ltr01.
    by move=>e he hr.
  - move=>A B [r [hr hA]] [s [hs hB]].
    exists (Num.min r s); split; first by rewrite lt_min hr hs.
    move=>e he; rewrite lt_min=>/andP[her hes]; split; [exact:hA e he her|exact:hB e he hes].
  - move=>A B hAB [r [hr hA]]; exists r; split=>//e he her.
    exact:hAB e (hA e he her).
have hAF:Filter (a @ F):=fmap_filter a hF.
have hWeak:open_family_converges O (a @ F) d.
  apply:(hO (a @ F) hAF d).2=>f W hW hWf.
  pose hR:=@scalar_absolute_value_norm R.
  have hNbhs:=@open_nbhs_nbhs [the topologicalType of real_norm_metric_space hR]
    (ev d f) W (conj hW hWf).
  have[eta hEta hBall]:=(metricType_numDomainType.nbhs_mdistP
    (ev d f:real_norm_metric_space hR) W).1 hNbhs.
  have[r [hr hBound]]:=hPoint f eta hEta.
  change (F (fun e=>W (ev (a e) f))).
  exists r; split=>//e he her; apply:hBall.
  change (is_true (`|ev d f-ev (a e) f|<eta)).
  rewrite (real_seminorm_subtract hR.1); exact:hBound e he her.
move=>V hV hVd.
exact:(hWeak V hV hVd).
Qed.
