(** Federer (1969), 3.1.19, p. 231: a submanifold is locally
    compact. In a coordinate neighbourhood it is the fixed set of
    the continuous local retraction. Closed finite-dimensional balls
    then give compact neighbourhoods in its actual relative topology. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology lra.
From Federer Require Import Hom LinearBasis RealNormUP NormMetric NormDifferentialUP
  NormRegularity NormCoordinateTopology RetractionUP FiniteNormEquivalence
  MetricSubsetBackground MetricSubsetCorestriction SubtypeCompactHausdorff
  IsotropyGroupTopology ContinuousEqualizerClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_local_retraction_compact_ball]: supporting
    local compactness in Federer 3.1.19, p. 231. The intersection
    of B with a sufficiently small closed ball is compact, because
    the retraction fixes exactly B inside its open domain. *)
Lemma norm_local_retraction_compact_ball (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) d (e:'I_d->X) (he:is_basis e)
    (B T:set X) (rho:X->X) k b :
  norm_domain_interior NX T b ->
  is_norm_class_retraction hNX T (B `&` T) rho k ->
  exists r:R, 0<r /\
    @compact [the topologicalType of real_norm_metric_space hNX]
      [set x|B x /\ NX (x-b)<=r].
Proof.
move=>[s [hs hball]] [hc hBT hinto hfix].
pose r:=s/2.
have hr:0<r by rewrite /r divr_gt0 // ltr0n.
have hrs:r<s by rewrite /r; lra.
pose M:=real_norm_metric_space hNX.
pose K:set M:=fun x=>NX (x-b)<=r.
have hKT:K `<=` T.
  move=>x hx; have hh:=hball (x-b) (le_lt_trans hx hrs).
  by rewrite addrC subrK in hh.
have hK:compact K:=@finite_norm_closed_ball_compact R X d e he NX hNX b r.
pose E:=metric_subset K.
pose C:set E:=fun z=>rho (val z)=val z.
have hcR:continuous (fun z:E=>(rho (val z):M)).
  exact (@norm_class_subdomain_continuous R X X NX NX hNX hNX T K rho k hKT hc).
have hCc:closed C.
  exact (@continuous_equalizer_closed E M (fun z=>rho (val z)) (fun z=>val z)
    (@metric_hausdorff R M) hcR (@metric_subset_inclusion_continuous R M K)).
have hCC:compact C.
  apply: (subclosed_compact hCc (set_type_compact_whole hK))=>z _; exact I.
have hCI:compact ((fun z:E=>(val z:M)) @` C).
  exact (@continuous_compact E M (fun z:E=>val z) C
    (continuous_subspaceT (@metric_subset_inclusion_continuous R M K)) hCC).
have hEq:((fun z:E=>(val z:M)) @` C)=[set x:M|B x /\ NX (x-b)<=r].
  apply/seteqP; split=>x.
  - move=>[z hz <-]; split; last exact (@set_valP M K z).
    have hh:=@hinto (val z) (@hKT (val z) (@set_valP M K z)).
    by rewrite hz in hh; exact hh.1.
  - move=>[hBx hKx].
    exists (@exist M (fun x=>x \in K) x (mem_set hKx)); last by [].
    change (rho x=x); exact: hfix (conj hBx (hKT x hKx)).
exists r; split=>//; by rewrite -hEq.
Qed.

(** Source for [finite_norm_locally_retracted_subset_compact]: the
    local compactness assertion in Federer 3.1.19, p. 231, in the
    general supporting form of a subset with local class-k retractions.
    Compactness is proved on the actual subtype, including empty B. *)
Theorem finite_norm_locally_retracted_subset_compact (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) d (e:'I_d->X) (he:is_basis e)
    (B:set X) k :
  (forall b, B b -> exists T rho, norm_domain_interior NX T b /\
    is_norm_class_retraction hNX T (B `&` T) rho k) ->
  locally_compact [set:metric_subset (fun x:real_norm_metric_space hNX=>B x)].
Proof.
move=>hB z _; rewrite withinET.
pose M:=real_norm_metric_space hNX.
pose S:=metric_subset (fun x:M=>B x).
have [T [rho [hTb hR]]]:=hB (val z) (set_valP z).
have [r [hr hK]]:=@norm_local_retraction_compact_ball R X NX hNX d e he B T rho k (val z) hTb hR.
pose K:set M:=fun x=>B x /\ NX (x-val z)<=r.
pose L:set S:=fun x=>K (val x).
have hLc:compact L.
  exact (@set_type_compact_preimage M B K hK (fun x hx=>hx.1)).
exists L.
- apply: (proj2 (metricType_numDomainType.nbhs_mdistP z L)).
  exists r=>// y hy; split; first exact: set_valP.
  have hh:NX (val z-val y)<r:=hy.
  rewrite (real_seminorm_subtract hNX.1) in hh; exact: ltW hh.
- split=>//; exact: compact_closed (@metric_hausdorff R S) hLc.
Qed.
