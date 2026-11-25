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

(** Source for [weak_directed_positive_parameter_limit]: the joint
    large-index and small-positive-parameter weak convergence used in
    Federer 4.1.2, p. 348. The thresholds work simultaneously,
    rather than depending on the chosen later index. *)
Theorem weak_directed_positive_parameter_limit (R:realType) (E D:choiceType)
    (ev:D->E->R) (O:set (set D)) (hO:is_weak_evaluation_convergence ev O)
    (a:nat->R->D) (d:D):
  (forall f eta,0<eta ->exists v:nat,exists r:R,0<r /\
    forall j,(v<=j)%N ->forall e:R,0<e ->e<r ->
      `|ev (a j e) f-ev d f|<eta) ->
  forall V,O V ->V d ->exists v:nat,exists r:R,0<r /\
    forall j,(v<=j)%N ->forall e:R,0<e ->e<r ->V (a j e).
Proof.
move=>hPoint.
pose F:set_system (nat*R)%type:=fun A=>exists v:nat,exists r:R,0<r /\
  forall j,(v<=j)%N ->forall e:R,0<e ->e<r ->A (j,e).
have hF:Filter F.
  constructor.
  - exists 0%N,1; split; first exact:ltr01.
    by move=>j hj e he hr.
  - move=>A B [v [r [hr hA]]] [w [s [hs hB]]].
    exists (maxn v w),(Num.min r s); split; first by rewrite lt_min hr hs.
    move=>j hj e he; rewrite lt_min=>/andP[her hes]; split.
    + exact:hA j (leq_trans (leq_maxl v w) hj) e he her.
    + exact:hB j (leq_trans (leq_maxr v w) hj) e he hes.
  - move=>A B hAB [v [r [hr hA]]]; exists v,r; split=>//j hj e he her.
    exact:hAB (j,e) (hA j hj e he her).
pose b:=fun p:(nat*R)%type=>a p.1 p.2.
have hBF:Filter (b @ F):=fmap_filter b hF.
have hWeak:open_family_converges O (b @ F) d.
  apply:(hO (b @ F) hBF d).2=>f W hW hWf.
  pose hR:=@scalar_absolute_value_norm R.
  have hNbhs:=@open_nbhs_nbhs [the topologicalType of real_norm_metric_space hR]
    (ev d f) W (conj hW hWf).
  have[eta hEta hBall]:=(metricType_numDomainType.nbhs_mdistP
    (ev d f:real_norm_metric_space hR) W).1 hNbhs.
  have[v [r [hr hBound]]]:=hPoint f eta hEta.
  change (F (fun p=>W (ev (a p.1 p.2) f))).
  exists v,r; split=>//j hj e he her; apply:hBall.
  change (is_true (`|ev d f-ev (a j e) f|<eta)).
  rewrite (real_seminorm_subtract hR.1); exact:hBound j hj e he her.
move=>V hV hVd.
exact:(hWeak V hV hVd).
Qed.
