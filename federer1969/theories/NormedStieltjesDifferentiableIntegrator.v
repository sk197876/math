(** Federer (1969), 3.1.11, pp. 220–221:
    equivalence of the ordinary and Stieltjes forms
    of the Taylor integral. A class-one scalar
    integrator is replaced by its derivative in
    the tagged sums of 2.5.17, pp. 110–111. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import RealNormUP StieltjesSums NormDifferentialUP NormClassOneUP
  NormHigherCurveDerivativeUP NormedStieltjesUP NormedStieltjesComparison
  NormedPrimitiveCell NormedSegmentUniformContinuity NormedSegmentBounded.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [normed_stieltjes_differentiable_integrator_sums]:
    the difference between the two kinds of
    Taylor sums tends to zero as the mesh
    tends to zero, Federer 3.1.11,
    pp. 220–221. Boundedness of the vector
    integrand suffices for this comparison. *)
Theorem normed_stieltjes_differentiable_integrator_sums (R : realType)
    (Y : lmodType R) (NY : Y->R) (hNY : is_real_norm NY)
    (A : R->Prop) (f : R->Y) (g v : R->R) (a b M : R) :
  a<=b -> 0<=M ->
  (forall t, a<=t<=b -> A t) ->
  (forall t, a<=t<=b -> NY (f t)<=M) ->
  (forall t, A t ->
    has_norm_differential (fun s : R^o=>`|s|)
      (fun s : R^o=>`|s|) A g t (@scalar_coefficient_linear_map R R^o (v t))) ->
  norm_class_zero (fun s : R^o=>`|s|) (fun s : R^o=>`|s|) A v ->
  forall e : R, 0<e -> exists d : R, 0<d /\
    forall w, is_tagged_partition a b w -> tagged_mesh_lt d w ->
      NY (normed_stieltjes_sum f g w-
        normed_stieltjes_sum (fun t=>v t*:f t) (fun t=>t) w)<e.
Proof.
move=> hab hM hA hbound hD hc e he.
have hwidth : 0<=b-a by rewrite subr_ge0.
have hden : 0<(M+1)*(b-a+1) by apply: mulr_gt0; lra.
pose eta := e/((M+1)*(b-a+1)).
have heta : 0<eta by rewrite /eta divr_gt0.
have [d [hd hmod]] := norm_class_zero_real_segment_uniform
  (@scalar_absolute_value_norm R) hA hc heta.
exists d; split=> // w hw hm.
have hcell p u q : a<=p -> p<=u -> u<=q -> q<=b -> q-p<d ->
    NY ((g q-g p)*:f u-(q-p)*:(v u*:f u))<=(eta*M)*(q-p).
  move=> hap hpu huq hqb hsmall.
  have hpuq s : p<=s<=q -> a<=s<=b.
    move=> /andP [hps hsq]; apply/andP; split;
      [exact: le_trans hap hps|exact: le_trans hsq hqb].
  have hu : a<=u<=b by apply: hpuq; apply/andP; split.
  have hosc s (hs : p<=s<=q) : `|v s-v u|<=eta.
    have /andP [hps hsq] := hs.
    have hsu : `|s-u|<=q-p by rewrite ler_norml; apply/andP; split; lra.
    exact: ltW (hmod s u (hpuq s hs) hu (le_lt_trans hsu hsmall)).
  have hstep := normed_primitive_cell_estimate (@scalar_absolute_value_norm R)
    hpu huq (ltW heta) (fun s hs=>hD s (hA s (hpuq s hs))) hosc.
  change (is_true (`|(q-p)*v u-(g q-g p)|<=eta*(q-p))) in hstep.
  rewrite scalerA -scalerBl (real_seminorm_scale hNY.1) distrC.
  apply: le_trans (ler_pM (normr_ge0 _) (real_seminorm_nonnegative hNY.1 _)
    hstep (hbound u hu)) _.
  have hid : (eta*(q-p))*M=(eta*M)*(q-p) by ring.
  by rewrite hid.
have hb := normed_stieltjes_partition_comparison hNY hcell hw hm.
have hfactor : M*(b-a)<(M+1)*(b-a+1) by nra.
have hlast : eta*(M*(b-a))<eta*((M+1)*(b-a+1)).
  by rewrite (ltr_pM2l heta).
have heq : eta*((M+1)*(b-a+1))=e by rewrite /eta divfK // gt_eqF.
rewrite heq mulrA in hlast; exact: le_lt_trans hb hlast.
Qed.

(** Source for [normed_stieltjes_differentiable_integrator]:
    integration against g equals integration against
    g' dt when g is class one on
    a neighborhood of the interval, supporting
    the exact Taylor formula of Federer 3.1.11,
    pp. 220–221. Existence is transferred
    in both directions, not assumed for all
    continuous vector integrands. *)
Theorem normed_stieltjes_differentiable_integrator (R : realType)
    (Y : lmodType R) (NY : Y->R) (hNY : is_real_norm NY)
    (A : R->Prop) (f : R->Y) (g v : R->R) (a b : R) (y : Y) :
  a<=b -> (forall t, a<=t<=b -> A t) ->
  norm_class_zero (fun s : R^o=>`|s|) NY A f ->
  (forall t, A t ->
    has_norm_differential (fun s : R^o=>`|s|)
      (fun s : R^o=>`|s|) A g t (@scalar_coefficient_linear_map R R^o (v t))) ->
  norm_class_zero (fun s : R^o=>`|s|) (fun s : R^o=>`|s|) A v ->
  (has_normed_stieltjes_integral NY f g a b y <->
   has_normed_stieltjes_integral NY (fun t=>v t*:f t) (fun t=>t) a b y).
Proof.
move=> hab hA hcf hD hcv.
have [M [hM hb]] := norm_class_zero_real_segment_bounded hNY hA hcf.
have hclose := normed_stieltjes_differentiable_integrator_sums
  hNY hab (ltW hM) hA hb hD hcv.
split.
- move=> hi; apply: (normed_stieltjes_integral_transfer hNY _ hi).
  move=> e he; have [d [hd hm]] := hclose e he.
  exists d; split=> // w hw hs.
  rewrite (real_seminorm_subtract hNY.1); exact: hm w hw hs.
- move=> hi; exact (normed_stieltjes_integral_transfer hNY hclose hi).
Qed.
