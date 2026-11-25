(** Federer (1969), 3.1.24, pp. 238–239:
    completeness of the continuous multilinear spaces used to
    sum the derivative series. The space is supplied by the
    abstract laws of 3.1.11, p. 219; its implementation
    is never imported. Only the target must be complete. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import Hom TensorFamilyUP FamilyUpdate RealNormUP NormMetric NormMetricContinuity NormMetricScaleContinuity
  CompleteMetricUP MetricLipschitzCauchy ContinuousMultilinearUP ContinuousMultilinearNorm
  ContinuousMultilinearCauchyUniform.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_multilinear_complete_general]: supporting
    existence of all derivative-series sums in Federer 3.1.24,
    pp. 238–239. Continuous k-linear maps into a Banach
    space form a Banach space for the corrected operator
    norm of 3.1.11, p. 219 (erratum p. 4,
    book p. 219 line 4). The argument uses pointwise
    limits and the product-weighted Cauchy estimate, includes
    k=0, and does not require finite-dimensional input. *)
Theorem continuous_multilinear_complete_general (R:realType) k
    (X Y Z:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (ev:{ffun 'I_k->X}->Hom Z Y) (ZN:Z->R)
    (hZ:is_continuous_multilinear_space NX NY ev ZN) :
  is_complete_metric_space (real_norm_metric_space hNY) ->
  is_complete_metric_space
    (real_norm_metric_space (continuous_multilinear_norm_is_norm hNY hZ)).
Proof.
move=>hY F PF hc.
pose E:=real_norm_metric_space (continuous_multilinear_norm_is_norm hNY hZ).
pose T:=real_norm_metric_space hNY.
have FF:Filter F:=@filter_filter _ F PF.
have hprod u:0<=\prod_(i<k) NX (u i).
  apply: prodr_ge0=>i _; exact: real_seminorm_nonnegative hNX.1 _.
have hex u:exists y:T,(fun z:E=>(ev u z:T)) @ F --> y.
  pose e:=fun z:E=>(ev u z:T).
  have PFe:ProperFilter (e @ F):=@fmap_proper_filter E T e F PF.
  apply: (hY (e @ F) PFe).
  apply: (@metric_lipschitz_cauchy_image R E T e (\prod_(i<k) NX (u i)) F PF)=>//.
  move=>z w.
  change (NY (ev u z-ev u w)<=(\prod_(i<k) NX (u i))*ZN (z-w)).
  have hh:=multilinear_operator_bound (continuous_multilinear_norm_laws hZ (z-w)) u.
  by rewrite linearB /= mulrC in hh.
have [g hg]:=choice hex.
have hlinear:multilinear (fun u=>(g u:Y)).
  move=>u i c x y.
  have hcx:(fun z:E=>(c*:ev (@family_with k (fun _ : 'I_k=>X) u i x) z:T)) @ F -->
      (c*:g (@family_with k (fun _ : 'I_k=>X) u i x):T).
    move=>U hU; exact: hg (@family_with k (fun _ : 'I_k=>X) u i x) _
      (@real_norm_metric_scale_continuous R Y NY hNY c (g (@family_with k (fun _ : 'I_k=>X) u i x)) U hU).
  have hp:=cvg_pair hcx (hg (@family_with k (fun _ : 'I_k=>X) u i y)).
  have hs:(fun z:E=>(c*:ev (@family_with k (fun _ : 'I_k=>X) u i x) z+ev (@family_with k (fun _ : 'I_k=>X) u i y) z:T)) @ F -->
      (c*:g (@family_with k (fun _ : 'I_k=>X) u i x)+g (@family_with k (fun _ : 'I_k=>X) u i y):T).
    move=>U hU; exact: hp _ (@real_norm_metric_add_continuous R Y NY hNY
      (c*:g (@family_with k (fun _ : 'I_k=>X) u i x),g (@family_with k (fun _ : 'I_k=>X) u i y)) U hU).
  have heq:(fun z:E=>(c*:ev (@family_with k (fun _ : 'I_k=>X) u i x) z+ev (@family_with k (fun _ : 'I_k=>X) u i y) z:T))=
      (fun z:E=>(ev (@family_with k (fun _ : 'I_k=>X) u i (c*:x+y)) z:T)).
    apply: funext=>z; symmetry; exact: continuous_multilinear_evaluation hZ z u i c x y.
  rewrite heq in hs.
  have PFx:ProperFilter ((fun z:E=>(ev (@family_with k (fun _ : 'I_k=>X) u i (c*:x+y)) z:T)) @ F):=
    @fmap_proper_filter E T (fun z=>(ev (@family_with k (fun _ : 'I_k=>X) u i (c*:x+y)) z:T)) F PF.
  exact (@cvg_unique T (@metric_hausdorff R T) _ PFx
    (g (@family_with k (fun _ : 'I_k=>X) u i (c*:x+y)))
    (c*:g (@family_with k (fun _ : 'I_k=>X) u i x)+g (@family_with k (fun _ : 'I_k=>X) u i y)) (hg _) hs).
have hunif:=@continuous_multilinear_cauchy_uniform R k X Y Z NX NY hNX hNY
  ev ZN hZ F (fun u=>(g u:Y)) PF hc hg.
have hgBound:norm_bounded_multilinear NX NY (fun u=>(g u:Y)).
  split; first exact hlinear.
  have [U hU hUb]:=hunif 1 ltr01.
  have [z hz]:=@filter_ex E F PF _ hU.
  exists (ZN z+1); split.
  - have hn:=multilinear_operator_nonnegative (continuous_multilinear_norm_laws hZ z); lra.
  - move=>u.
    have h1:=hUb z hz u.
    rewrite mul1r (real_seminorm_subtract hNY.1) in h1.
    have h2:=multilinear_operator_bound (continuous_multilinear_norm_laws hZ z) u.
    have h3:=real_seminorm_triangle hNY.1 (g u-ev u z) (ev u z).
    rewrite subrK in h3.
    have hh:=le_trans h3 (lerD h1 h2).
    by rewrite mulrDl mul1r addrC.
have [z hz]:=continuous_multilinear_surjective hZ hgBound.
exists (z:E)=>W hW.
have [e he hb]:=proj1 (metricType_numDomainType.nbhs_mdistP (z:E) W) hW.
have he2:0<e/2 by rewrite divr_gt0 // ltr0n.
have [U hU hUb]:=hunif (e/2) he2.
apply: (@filterS E F FF _ _ _ hU)=>w hw; apply: hb.
change (ZN (z-w)<e).
have hsmall:ZN (z-w)<=e/2.
  apply: (multilinear_operator_least (continuous_multilinear_norm_laws hZ (z-w)) (ltW he2)).
  move=>u; rewrite linearB /= hz.
  rewrite (real_seminorm_subtract hNY.1); exact: hUb w hw u.
lra.
Qed.
