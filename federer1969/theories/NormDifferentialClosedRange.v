(** Federer (1969), 3.1.1, pp. 209, 211: directional quotients
    show that the differential also takes values in the closed
    linear subspace used for the separable-target reduction. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology lra.
From Federer Require Import Hom ModuleQuotient RealNormUP NormMetric
  NormDifferentialUP NormDifferentialDirectional NormedCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [punctured_norm_limit_closed_member]: supporting
    closed-set limit fact for the directional formula on p. 209
    and the target reduction on p. 211 of 3.1.1. *)
Lemma punctured_norm_limit_closed_member (R : realType) (Y : lmodType R)
    (N : Y -> R) (hN : is_real_norm N) (C : set Y) (u : R -> Y) (v : Y) :
  @closed [the topologicalType of real_norm_metric_space hN] C ->
  punctured_norm_limit N u v ->
  (exists r : R, 0<r /\ forall t, 0<`|t|<r -> C (u t)) -> C v.
Proof.
move=> hC hv [r [hr hu]]; apply: hC=> W hW.
have [e he hb] := proj1 (metricType_numDomainType.nbhs_mdistP (v : real_norm_metric_space hN) W) hW.
have [d [hd hlim]] := hv e he.
pose t := Num.min r d/2.
have hm : 0<Num.min r d by rewrite lt_min hr hd.
have ht : 0<t by rewrite /t divr_gt0.
have hsmall : t<Num.min r d by rewrite /t; lra.
have /andP [htr htd] : (t<r)&&(t<d) by rewrite -lt_min.
have hnorm : `|t|=t := ger0_norm (ltW ht).
have hCt : C (u t) by apply: hu; rewrite hnorm ht htr.
exists (u t); split=> //; apply: hb.
change (N (v-u t)<e); rewrite (real_seminorm_subtract hN.1).
apply: hlim; by rewrite hnorm ht htd.
Qed.

(** Source for [norm_differential_closed_linear_range]: the
    differential has its image in the same closed linear target
    subspace as f, as required by the reduction in 3.1.1,
    p. 211. This uses the actual directional limits of p. 209. *)
Theorem norm_differential_closed_linear_range (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (A : set X) (f : X -> Y) (a : X) (L : Hom X Y) (S : subspace Y) :
  @closed [the topologicalType of real_norm_metric_space hNY] (fun y=>S y) ->
  (forall x, A x -> S (f x)) -> has_norm_differential NX NY A f a L ->
  forall v, S (L v).
Proof.
move=> hS hf hD v.
apply: (@punctured_norm_limit_closed_member R Y NY hNY S
  (fun t=>t^-1 *: (f (a+t *: v)-f a)) (L v) hS
  (norm_differential_directional_limit hNX hNY hD v)).
have [r [hr hA]] := norm_differential_interior hD.
have hn := real_seminorm_nonnegative hNX.1 v.
have hp : 0<NX v+1 by lra.
exists (r/(NX v+1)); split; first by rewrite divr_gt0.
move=> t /andP [ht hs]; apply: subspace_scale; apply: subspace_sub.
- apply: hf; apply: hA; rewrite (real_seminorm_scale hNX.1).
  have hlarge : `|t|*(NX v+1)<r by rewrite -ltr_pdivlMr.
  nra.
- exact: (hf a (@norm_domain_interior_member R X NX hNX A a (norm_differential_interior hD))).
Qed.
