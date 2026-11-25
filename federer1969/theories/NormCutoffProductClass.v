(** Federer (1969), 3.1.22, p. 236: multiply
    a local extension by a subordinate smooth partition function. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  NormRegularity NormRegularityOperations NormRegularityLocal NormRegularityBilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_class_cutoff_product]: supporting the
    partition-of-unity extension argument in Federer 3.1.22,
    p. 236. A class-k local function multiplied
    by a global class-k cutoff vanishing outside a closed
    subset of its domain is globally class k. The original
    total representative outside its actual domain is immaterial. *)
Lemma norm_class_cutoff_product (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (T P:set X) (u:X->R^o) (g:X->Y) k :
  norm_class hNX hNY T g k ->
  norm_class hNX (scalar_absolute_value_norm R) setT u k ->
  @closed (real_norm_metric_space hNX) P -> P `<=` T ->
  (forall x,~P x -> u x=0) ->
  norm_class hNX hNY setT (fun x=>u x*:g x) k.
Proof.
move=>hg hu hP hPT hu0.
apply: (@norm_class_local_representatives R X Y NX NY hNX hNY setT (fun x=>u x*:g x) k)=>a _.
case:(pselect (T a))=>[haT|haT].
- have hTint x (hx:T x):norm_domain_interior NX T x.
    exact ((@norm_class_continuous R X Y NX NY hNX hNY T g k hg x hx).1).
  have huT:=@norm_class_open_restriction R X R^o NX (fun t:R^o=>`|t|) hNX
    (scalar_absolute_value_norm R) setT T u k (fun _ _=>I) hTint hu.
  exists T,(fun x=>u x*:g x); split=>//; split; first by move=>x _.
  split; first exact: norm_class_scalar_product huT hg.
  by move=>x _.
- pose O:=fun x=>~P x.
  have haO:O a by move=>haP; exact: haT (hPT a haP).
  have hO:@open (real_norm_metric_space hNX) O:=closed_openC hP.
  have hOint x (hx:O x):norm_domain_interior NX O x.
    exact ((@norm_domain_interior_neighbourhood R X NX hNX O x).2
      (open_nbhs_nbhs (conj hO hx))).
  have hz:=@norm_class_constant R X Y NX NY hNX hNY O 0 k hOint.
  exists O,(fun _=>0); split=>//; split; first by move=>x _.
  split; first exact hz.
  move=>x hx; by rewrite (hu0 x hx) scale0r.
Qed.
