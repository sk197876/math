(** Federer (1969), 3.4.5, p. 319: existence,
    representative independence and uniqueness of every actual germ jet. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity NormBoundedLinearTopology
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP
  NormHigherDifferentialLocal NormHigherDifferentialUnique LocalGermUP LocalGermSealed
  AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRingLaws AnalyticGermJetsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Jets.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable a:X.
Local Notation NS:=(fun t:R^o=>`|t|).
Local Notation hNS:=(@scalar_absolute_value_norm R).
Local Notation Z:=(fun m=>@ContinuousMultilinear.space R m X R^o NX NS hNX hNS).
Local Notation ev:=(fun m=>@ContinuousMultilinear.evaluation R m X R^o NX NS hNX hNS).
Local Notation ZN:=(fun m=>@ContinuousMultilinear.norm R m X R^o NX NS hNX hNS).
Local Notation P:=(@analytic_representative_type R X NX hNX a).
Local Notation value:=(@analytic_representative_value R X NX hNX a).
Local Notation G:=(analytic_germ_space hNX a).
Local Notation germ:=(@analytic_germ R X NX hNX a).

(** Source for [analytic_representative_higher_exists]: analyticity
    supplies every actual differential at the centre, 3.4.5,
    p. 319, by the original local smoothness of 3.1.24. *)
Lemma analytic_representative_higher_exists (f:P) m:
  exists z:Z m,has_norm_higher_differential NX ev ZN setT (value f) m a z.
Proof.
have [U [c [ha [hUT [hClass hBound]]]]]:=analytic_representative_analytic f.
have [D [hD hDContinuous]]:=(hClass m).2.
have hOpen x (hx:U x):norm_domain_interior NX U x:=((hClass 0%N).1 x hx).1.
have hZ i:is_continuous_multilinear_space NX NS (ev i) (ZN i):=@ContinuousMultilinear.laws R i X R^o NX NS hNX hNS.
exists (D a).
exact:((@norm_higher_differential_open_restriction R X R^o NX NS hNX hNS Z ev ZN hZ
  m setT U (value f) hUT hOpen a ha (D a)).2 (hD a ha)).
Qed.

(** Source for [analytic_germ_higher_representative_independence]:
    equal germs have exactly the same actual m-th differential
    graph at a, 3.4.5, p. 319. The proof uses
    only local agreement and the proved local higher-differential law. *)
Lemma analytic_germ_higher_representative_independence (f g:P) m (z:Z m):
  germ f=germ g ->
  (has_norm_higher_differential NX ev ZN setT (value f) m a z <->
   has_norm_higher_differential NX ev ZN setT (value g) m a z).
Proof.
move/(local_germ_equality (@LocalGerms.laws
  (Topological.clone (real_norm_metric_space hNX) _) R P value a))=>[U [hU [ha hEq]]].
have hOpen x (hx:U x):norm_domain_interior NX U x.
  rewrite openE in hU;exact:((@norm_domain_interior_neighbourhood R X NX hNX U x).2 (hU x hx)).
have hZ i:is_continuous_multilinear_space NX NS (ev i) (ZN i):=@ContinuousMultilinear.laws R i X R^o NX NS hNX hNS.
exact:(@norm_higher_differential_local_agreement R X R^o NX NS hNX hNS Z ev ZN hZ
  m setT setT U (value f) (value g) hOpen (fun x hx=>iff_refl _) (fun x hx _=>hEq x hx) a ha z).
Qed.

(** Source for [analytic_germ_jet_exists]: the original
    m-th differential D^m(alpha) in 3.4.5, p. 319,
    exists and satisfies the independent all-representative laws. *)
Theorem analytic_germ_jet_exists m (alpha:G):exists z:Z m,is_analytic_germ_jet alpha z.
Proof.
have [f hf]:=@analytic_germ_has_representative R X NX hNX a alpha.
have [z hz]:=analytic_representative_higher_exists f m.
exists z=>g hg.
have hEqual:germ f=germ g by rewrite hf hg.
exact:((@analytic_germ_higher_representative_independence f g m z hEqual).1 hz).
Qed.

(** Source for [analytic_germ_jet_unique]: the m-th actual
    differential attached to a germ is unique, 3.4.5, p. 319. *)
Lemma analytic_germ_jet_unique m (alpha:G) (z w:Z m):
  is_analytic_germ_jet alpha z ->is_analytic_germ_jet alpha w ->z=w.
Proof.
move=>hz hw;have [f hf]:=@analytic_germ_has_representative R X NX hNX a alpha.
have hZ i:is_continuous_multilinear_space NX NS (ev i) (ZN i):=@ContinuousMultilinear.laws R i X R^o NX NS hNX hNS.
exact:(@norm_higher_differential_unique R X R^o NX NS hNX hNS Z ev ZN hZ
  setT (value f) m a z w (hz f hf) (hw f hf)).
Qed.
End Jets.
