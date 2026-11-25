(** Federer (1969), 3.1.11, p. 220:
    continuous operators into a Banach space form a Banach
    space in the operator norm. Unlike the finite-coordinate
    result of 3.1.1, no finite dimension of the source is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormMetricContinuity
  NormMetricScaleContinuity NormDifferentialUP NormOperatorNormUP ContinuousOperatorUP
  ContinuousOperatorNorm ContinuousOperatorEvaluation
  ContinuousOperatorCauchyUniform CompleteMetricUP MetricLipschitzCauchy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_operator_complete_general]:
    the Banach space of continuous endomorphisms of X
    in Federer 3.1.11, p. 220. The stronger supporting
    result below only requires completeness of the target Y;
    the source X may be any normed space. The operator
    carrier is used solely through its abstract laws. *)
Theorem continuous_operator_complete_general (R : realType)
    (X Y Z : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (evaluation : Hom Z (Hom X Y)) (ZN : Z->R)
    (hZ : is_continuous_operator_space NX NY evaluation ZN) :
  is_complete_metric_space (real_norm_metric_space hNY) ->
  is_complete_metric_space
    (real_norm_metric_space (continuous_operator_norm_is_norm hNY hZ)).
Proof.
move=> hY F PF hc.
pose E := real_norm_metric_space (continuous_operator_norm_is_norm hNY hZ).
pose T := real_norm_metric_space hNY.
have FF : Filter F := @filter_filter _ F PF.
have hex x : exists y : T, (fun z : E=>(evaluation z x : T)) @ F --> y.
  pose ev := fun z : E=>(evaluation z x : T).
  have PFe : ProperFilter (ev @ F) := @fmap_proper_filter E T ev F PF.
  apply: (hY (ev @ F) PFe).
  apply: (@metric_lipschitz_cauchy_image R E T ev (NX x) F PF)=> //.
  - exact: real_seminorm_nonnegative hNX.1 x.
  - exact: continuous_operator_evaluation_distance.
have [g hg] := choice hex.
have hlinear : linear (fun x=>(g x : Y)).
  move=> c x y.
  have hcx : (fun z : E=>(c*:evaluation z x : T)) @ F --> (c*:g x : T).
    move=> U hU.
    have hh := hg x _ (@real_norm_metric_scale_continuous R Y NY hNY c (g x) U hU).
    exact hh.
  have hp := cvg_pair hcx (hg y).
  have hs : (fun z : E=>(c*:evaluation z x+evaluation z y : T)) @ F -->
      (c*:g x+g y : T).
    move=> U hU; exact: hp _ (@real_norm_metric_add_continuous R Y NY hNY (c*:g x,g y) U hU).
  have heq : (fun z : E=>(c*:evaluation z x+evaluation z y : T))=
      (fun z : E=>(evaluation z (c*:x+y) : T)).
    apply: funext=> z; by rewrite linearP.
  rewrite heq in hs.
  have PFx : ProperFilter ((fun z : E=>(evaluation z (c*:x+y) : T)) @ F) :=
    @fmap_proper_filter E T (fun z=>(evaluation z (c*:x+y) : T)) F PF.
  exact: (@cvg_unique T (@metric_hausdorff R T) _ PFx
    (g (c*:x+y)) (c*:g x+g y) (hg (c*:x+y)) hs).
pose L := @HomMap R X Y (fun x=>(g x : Y)) (introT (asboolP _) hlinear).
have hunif := @continuous_operator_cauchy_uniform R X Y Z NX NY hNX hNY
  evaluation ZN hZ F (fun x=>(g x : Y)) PF hc hg.
have hL : norm_bounded_linear NX NY L.
  have [U hU hUb] := hunif 1 ltr01.
  have [u hu] := @filter_ex E F PF _ hU.
  exists (ZN u+1); split.
  - have hn := norm_operator_nonnegative (continuous_operator_norm_laws hZ u); lra.
  - move=> x.
    have h1 := hUb u hu x.
    rewrite mul1r (real_seminorm_subtract hNY.1) in h1.
    have h2 := norm_operator_bound (continuous_operator_norm_laws hZ u) x.
    have h3 := real_seminorm_triangle hNY.1 (g x-evaluation u x) (evaluation u x).
    rewrite subrK in h3.
    change (NY (g x)<=(ZN u+1)*NX x).
    have hh := le_trans h3 (lerD h1 h2).
    by rewrite mulrDl mul1r addrC.
have [z hz] := continuous_operator_surjective hZ hL.
exists (z : E)=> W hW.
have [e he hball] := proj1 (metricType_numDomainType.nbhs_mdistP (z : E) W) hW.
have he2 : 0<e/2 by rewrite divr_gt0 // ltr0n.
have [U hU hUb] := hunif (e/2) he2.
apply: (@filterS E F FF _ _ _ hU)=> u hu; apply: hball.
change (ZN (z-u)<e).
have hsmall : ZN (z-u)<=e/2.
  apply: (norm_operator_least (continuous_operator_norm_laws hZ (z-u)) (ltW he2)).
  move=> x.
  rewrite linearB /= hz.
  change (NY (g x-evaluation u x)<=(e/2)*NX x).
  rewrite (real_seminorm_subtract hNY.1); exact: hUb u hu x.
lra.
Qed.
