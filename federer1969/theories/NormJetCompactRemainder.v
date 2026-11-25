(** Federer (1969), 3.1.11, p. 221:
    compact-uniform Taylor remainders expressed using
    the abstract jet polynomial, including order zero.
    The source segment follows the erratum correction. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import Hom RealNormUP NormMetric PolynomialFunctions
  ContinuousMultilinearUP NormHigherDifferentialUnique NormClassHigherUP
  NormTaylorRemainderBound NormTaylorCompactRemainder
  CompactNormDomainRadius CompactNearbyUniformContinuity NormJetUP NormJetRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_jet_compact_uniform_remainder]:
    the compact-uniform little-o remainder of
    the kth jet, Federer 3.1.11,
    p. 221, first with j= 0.
    Multiplication by k! preserves the printed
    normalization; the inequality includes zero increments. *)
Theorem norm_jet_compact_uniform_remainder (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A K : set X) (f : X->Y) k :
  norm_class_higher NX NY ev ZN A f k ->
  compact [set x : real_norm_metric_space hNX | K x] ->
  K `<=` A ->
  forall e : R, 0<e -> exists d : R, 0<d /\
    forall a v (P : PolynomialFunction X Y),
      K a -> NX v<d -> is_norm_jet_polynomial NX ev ZN A f k a P ->
      A (a+v) /\ NY (f (a+v)-P (a+v))*((k`!)%:R)<=e*(NX v)^+k.
Proof.
case:k=>[|k] hc hK hKA e he.
- have [r [hr hrA]] := @norm_compact_uniform_domain_radius R X NX hNX A K hK
    (fun a ha=>(hc.1 a (hKA a ha)).1).
  have [s [hs hcont]] := @norm_class_zero_compact_uniform_nearby R X Y NX NY
    hNX hNY A K f hK hKA hc.1 e he.
  exists (Num.min r s); split; first by rewrite lt_min hr hs.
  move=>a v P ha hv hP.
  have /andP [hvr hvs] : (NX v<r) && (NX v<s) by move:hv; rewrite lt_min.
  have hav := hrA a v ha hvr; split; first exact hav.
  rewrite (norm_zero_jet_value hP) /= mulr1 expr0 mulr1.
  apply: ltW; apply: (hcont a (a+v) ha hav).
  have hvv : a+v-a=v by rewrite addrAC subrr add0r.
  by rewrite hvv.
- have [D [hD hrem]] := norm_class_higher_taylor_compact_uniform hNX hNY hZ hc.
  have [d [hd hb]] := hrem K hK hKA e he.
  exists d; split=>// a v P ha hv hP.
  have [hav hbound] := hb a v ha hv.
  have [E [hE heP]] := norm_jet_polynomial_expansion hP.
  have hvalue : P (a+v)=norm_taylor_value ev D a v k.+1.
    rewrite heP.
    have hvv : a+v-a=v by rewrite addrAC subrr add0r.
    rewrite hvv /norm_taylor_value.
    apply: eq_bigr=>i _.
    have hi : (i<=k.+1)%N by move:(ltn_ord i); rewrite ltnS.
    have hsame := norm_higher_differential_unique hNX hNY hZ
      (hE i hi) (hD i hi a (hKA a ha)).
    by rewrite hsame.
  split; first exact hav; by rewrite hvalue.
Qed.
