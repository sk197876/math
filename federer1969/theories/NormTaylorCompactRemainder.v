(** Federer (1969), 3.1.11, p. 221:
    the remainder of the Taylor polynomial tends
    to zero uniformly as its base point ranges
    over a compact subset of the open domain.
    This file first treats the function value;
    derivative jets use the same estimate on D^j f. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets topology lra.
From Federer Require Import Hom RealNormUP NormMetric ContinuousMultilinearUP
  ContinuousMultilinearNorm NormHigherDifferentialUP NormClassOneUP
  NormClassHigherUP NormClassHigherFields CompactNearbyUniformContinuity
  CompactNormDomainRadius NormTaylorRemainderBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_taylor_remainder_compact_uniform_fields]:
    Federer 3.1.11, p. 221, the
    compact-uniform little-o assertion for j= 0,
    stated without division by the increment norm.
    The bound includes zero increments and keeps
    the exact factorial from the book. *)
Theorem norm_taylor_remainder_compact_uniform_fields (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A K : set X) (f : X->Y) (D : forall i, X->Z i) k :
  (forall i, (i<=k.+1)%N -> forall x, A x ->
    has_norm_higher_differential NX ev ZN A f i x (D i x)) ->
  norm_class_zero NX (@ZN k.+1) A (D k.+1) ->
  compact [set x : real_norm_metric_space hNX | K x] ->
  K `<=` A ->
  forall e : R, 0<e -> exists d : R, 0<d /\
    forall a v, K a -> NX v<d ->
      A (a+v) /\
      NY (f (a+v)-norm_taylor_value ev D a v k.+1)*((k.+1)`!)%:R<=
        e*(NX v)^+k.+1.
Proof.
move=> hD hc hK hKA e he.
have hnorm := continuous_multilinear_norm_is_norm hNY (@hZ k.+1).
have [r [hr hrA]] := @norm_compact_uniform_domain_radius R X NX hNX A K hK
  (fun a ha=>(hc a (hKA a ha)).1).
have [s [hs hcont]] := @norm_class_zero_compact_uniform_nearby R X (Z k.+1) NX (@ZN k.+1)
  hNX hnorm A K (D k.+1) hK hKA hc e he.
exists (Num.min r s); split; first by rewrite lt_min hr hs.
move=> a v ha hv.
have hvr : NX v<r.
  apply: lt_le_trans hv _; by rewrite ge_min lexx.
have hvs : NX v<s.
  apply: lt_le_trans hv _; by rewrite ge_min lexx orbT.
have hscale t (ht : 0<=t<= 1) : NX (t*:v)<=NX v.
  have /andP [ht0 ht1] := ht.
  rewrite (real_seminorm_scale hNX.1) (ger0_norm ht0).
  have hh := ler_wpM2r (real_seminorm_nonnegative hNX.1 v) ht1.
  by rewrite mul1r in hh.
have hseg t (ht : 0<=t<= 1) : A (a+t*:v).
  exact: hrA a (t*:v) ha (le_lt_trans (hscale t ht) hvr).
have hosc t (ht : 0<=t<= 1) :
    @ZN k.+1 (D k.+1 (a+t*:v)-D k.+1 a)<=e.
  apply: ltW; apply: (hcont a (a+t*:v) ha (hseg t ht)).
  have heq : a+t*:v-a=t*:v by rewrite addrAC subrr add0r.
  rewrite heq; exact: le_lt_trans (hscale t ht) hvs.
split; first exact: hrA a v ha hvr.
have hb := norm_taylor_remainder_oscillation_bound hNX hNY hZ hD hc hseg hosc.
have hfac : (0:R)<((k.+1)`!)%:R by rewrite ltr0n fact_gt0.
by rewrite ler_pdivlMr // in hb.
Qed.

(** Source for [norm_class_higher_taylor_compact_uniform]:
    the class-k hypothesis supplies the actual
    differential fields in the compact-uniform Taylor
    remainder, Federer 3.1.11, p. 221.
    No choice of polynomial coefficients is added
    to the theorem's hypotheses. *)
Theorem norm_class_higher_taylor_compact_uniform (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A : set X) (f : X->Y) k :
  norm_class_higher NX NY ev ZN A f k.+1 ->
  exists D : forall i, X->Z i,
    (forall i, (i<=k.+1)%N -> forall x, A x ->
      has_norm_higher_differential NX ev ZN A f i x (D i x)) /\
    forall K : set X,
      compact [set x : real_norm_metric_space hNX | K x] -> K `<=` A ->
      forall e : R, 0<e -> exists d : R, 0<d /\
      forall a v, K a -> NX v<d ->
        A (a+v) /\
        NY (f (a+v)-norm_taylor_value ev D a v k.+1)*((k.+1)`!)%:R<=
          e*(NX v)^+k.+1.
Proof.
move=> hk.
have [D [hD hc]] := norm_class_higher_fields hNX hNY hZ hk.
exists D; split; first exact hD.
move=> K hK hKA e he.
exact (@norm_taylor_remainder_compact_uniform_fields R X Y NX NY hNX hNY
  Z ev ZN hZ A K f D k hD (hc k.+1 (leqnn _)) hK hKA e he).
Qed.
