(** Federer (1969), 3.4.12, p. 339: existence,
    representative independence and uniqueness of every actual germ jet. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm NormMetric NormDifferentialUP NormRegularity NormAnalyticLocal NormBoundedLinearTopology
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP
  NormHigherDifferentialLocal NormHigherDifferentialUnique LocalGermUP LocalGermSealed
  HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRingLaws HolomorphicGermJetsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Jets.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Variable NX:XR->R.
Hypothesis hNX:is_real_norm NX.
Variable a:X.
Local Notation NS:=(@complex_modulus R).
Local Notation hNS:=(@complex_modulus_real_norm R).
Local Notation Z:=(fun m=>@ContinuousMultilinear.space R m XR CR NX NS hNX hNS).
Local Notation ev:=(fun m=>@ContinuousMultilinear.evaluation R m XR CR NX NS hNX hNS).
Local Notation ZN:=(fun m=>@ContinuousMultilinear.norm R m XR CR NX NS hNX hNS).
Local Notation P:=(@holomorphic_representative_type R X NX hNX a).
Local Notation value:=(@holomorphic_representative_value R X NX hNX a).
Local Notation G:=(holomorphic_germ_space hNX a).
Local Notation germ:=(@holomorphic_germ R X NX hNX a).

(** Source for [holomorphic_representative_higher_exists]: holomorphicity
    supplies every actual differential at the centre, 3.4.12,
    p. 339, by the original local smoothness of 3.1.24. *)
Lemma holomorphic_representative_higher_exists (f:P) m:
  exists z:Z m,has_norm_higher_differential NX ev ZN setT (value f) m a z.
Proof.
have [U [ha hF]]:=holomorphic_representative_holomorphic f.
have hClass:=norm_analytic_class_all_orders hF.1.
have hUT x (_:U x):setT x:=Logic.I.
have [D [hD hDContinuous]]:=(hClass m).2.
have hOpen x (hx:U x):norm_domain_interior NX U x:=((hClass 0%N).1 x hx).1.
have hZ i:@is_continuous_multilinear_space R i XR CR (Z i) NX NS (ev i) (ZN i):=@ContinuousMultilinear.laws R i XR CR NX NS hNX hNS.
exists (D a).
exact:((@norm_higher_differential_open_restriction R XR CR NX NS hNX hNS Z ev ZN hZ
  m setT U (value f) hUT hOpen a ha (D a)).2 (hD a ha)).
Qed.

(** Source for [holomorphic_germ_higher_representative_independence]:
    equal germs have exactly the same actual m-th differential
    graph at a, 3.4.12, p. 339. The proof uses
    only local agreement and the proved local higher-differential law. *)
Lemma holomorphic_germ_higher_representative_independence (f g:P) m (z:Z m):
  germ f=germ g ->
  (has_norm_higher_differential NX ev ZN setT (value f) m a z <->
   has_norm_higher_differential NX ev ZN setT (value g) m a z).
Proof.
move/(local_germ_equality (@LocalGerms.laws
  (Topological.clone (real_norm_metric_space hNX) _) C P value a))=>[U [hU [ha hEq]]].
have hOpen x (hx:U x):norm_domain_interior NX U x.
  rewrite openE in hU;exact:((@norm_domain_interior_neighbourhood R XR NX hNX U x).2 (hU x hx)).
have hZ i:@is_continuous_multilinear_space R i XR CR (Z i) NX NS (ev i) (ZN i):=@ContinuousMultilinear.laws R i XR CR NX NS hNX hNS.
exact:(@norm_higher_differential_local_agreement R XR CR NX NS hNX hNS Z ev ZN hZ
  m setT setT U (value f) (value g) hOpen (fun x hx=>iff_refl _) (fun x hx _=>hEq x hx) a ha z).
Qed.

(** Source for [holomorphic_germ_jet_exists]: the original
    m-th differential D^m(alpha) in 3.4.12, p. 339,
    exists and satisfies the independent all-representative laws. *)
Theorem holomorphic_germ_jet_exists m (alpha:G):exists z:Z m,is_holomorphic_germ_jet alpha z.
Proof.
have [f hf]:=@holomorphic_germ_has_representative R X NX hNX a alpha.
have [z hz]:=holomorphic_representative_higher_exists f m.
exists z=>g hg.
have hEqual:germ f=germ g by rewrite hf hg.
exact:((@holomorphic_germ_higher_representative_independence f g m z hEqual).1 hz).
Qed.

(** Source for [holomorphic_germ_jet_unique]: the m-th actual
    differential attached to a germ is unique, 3.4.12, p. 339. *)
Lemma holomorphic_germ_jet_unique m (alpha:G) (z w:Z m):
  is_holomorphic_germ_jet alpha z ->is_holomorphic_germ_jet alpha w ->z=w.
Proof.
move=>hz hw;have [f hf]:=@holomorphic_germ_has_representative R X NX hNX a alpha.
have hZ i:@is_continuous_multilinear_space R i XR CR (Z i) NX NS (ev i) (ZN i):=@ContinuousMultilinear.laws R i XR CR NX NS hNX hNS.
exact:(@norm_higher_differential_unique R XR CR NX NS hNX hNS Z ev ZN hZ
  setT (value f) m a z w (hz f hf) (hw f hf)).
Qed.
End Jets.
