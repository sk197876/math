(** Federer (1969), 3.1.11, p. 222: replacing the two maps
    by their jets in a composition gives a negligible remainder.
    The estimates use the sealed jet laws and local Lipschitz
    continuity, without completeness or finite-dimensionality. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP PolynomialFunctions
  ContinuousMultilinearUP NormClassOneUP NormClassHigherUP NormClassHigherLaws
  NormClassHigherFirst NormJetUP NormJet NormJetBaseValue NormJetLocalRemainder
  NormJetLineRemainder NormClassOneLocalLipschitz NormClassOneLineGrowth
  NormLittleOPower NormLittleOPullback NormLittleODomination.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CompositionRemainder.
Variable R : realType.
Variables X Y T : lmodType R.
Variables (NX : X->R) (NY : Y->R) (NT : T->R).
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.
Hypothesis hNT : is_real_norm NT.
Variables Z W : nat->lmodType R.
Variable ez : forall i, {ffun 'I_i->X}->Hom (Z i) Y.
Variable ZN : forall i, Z i->R.
Variable ew : forall i, {ffun 'I_i->Y}->Hom (W i) T.
Variable WN : forall i, W i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space NX NY (@ez i) (@ZN i).
Hypothesis hW : forall i, is_continuous_multilinear_space NY NT (@ew i) (@WN i).
Variables (A : X->Prop) (B : Y->Prop) (f : X->Y) (g : Y->T).
Variables (k : nat) (a : X).
Variables (P : PolynomialFunction X Y) (Q : PolynomialFunction Y T).
Hypothesis hk : (1<=k)%N.
Hypothesis ha : A a.
Hypothesis hb : B (f a).
Hypothesis hf : norm_class_higher NX NY ez ZN A f k.
Hypothesis hg : norm_class_higher NY NT ew WN B g k.
Hypothesis hP : is_norm_jet_polynomial NX ez ZN A f k a P.
Hypothesis hQ : is_norm_jet_polynomial NY ew WN B g k (f a) Q.

(** Source for [norm_outer_jet_pullback_remainder]: the difference
    between g(f(x)) and Q(f(x)) is negligible to order k at a,
    along each source line, Federer 3.1.11, p. 222. *)
Lemma norm_outer_jet_pullback_remainder v :
  norm_little_o_power NT
    (fun t=>g (f (a+t*:v))-Q (f (a+t*:v))) k.
Proof.
have hf1 := norm_class_higher_lower hNX hNY hZ hk hf.
have hfc := (norm_class_higher_first hNX hNY hZ A f).1 hf1.
have [C [r [hC [hr hbnd]]]] := norm_class_one_line_growth hNX hNY v ha hfc.
pose rho y := g (f a+y)-Q (f a+y).
have hrem e (he : 0<e) : exists d : R, 0<d /\
    forall y, NY y<d -> NT (rho y)<=e*(NY y)^+k.
  have [d [hd hh]] := norm_jet_local_remainder hNY hNT hW hb hg hQ he.
  exists d; split=> // y hy; exact: (hh y hy).2.
have hh := norm_little_o_power_pullback hNY
  (rho:=rho) (v:=fun t=>f (a+t*:v)-f a) hC hr
  (fun t ht=>(hbnd t ht).2) hrem.
move=>e he; have [d [hd hdB]] := hh e he.
exists d; split=> // t ht.
have heq : f a+(f (a+t*:v)-f a)=f (a+t*:v) by rewrite addrC subrK.
have htB := hdB t ht; by rewrite /rho heq in htB.
Qed.

(** Source for [norm_inner_jet_polynomial_remainder]: replacing
    f(x) by P(x) inside the outer polynomial changes its value by
    o(|t|^k) along x=a+t v, Federer 3.1.11, p. 222. *)
Lemma norm_inner_jet_polynomial_remainder v :
  norm_little_o_power NT
    (fun t=>Q (f (a+t*:v))-Q (P (a+t*:v))) k.
Proof.
have hQ1 := norm_jet_class_infinity hNY hNT hW hQ 1%N.
have hQc := (norm_class_higher_first hNY hNT hW (fun _=>True) Q).1 hQ1.
have [C [d [hC [hd [_ hLip]]]]] :=
  @norm_class_one_local_lipschitz R Y T NY NT hNY hNT (fun _=>True) Q (f a) I hQc.
have [r [hr hrB]] := norm_class_zero_line_small hNX v ha hf.1 hd.
have hP0 := (norm_jet_class_infinity hNX hNY hZ hP 0%N).1.
have [s [hs hsB]] := @norm_class_zero_line_small R X Y NX NY hNX
  (fun _=>True) P a v I hP0 d hd.
have heP := norm_jet_base_value hNX hNY hZ hP.
have hbound t : 0<`|t|<Num.min r s ->
    NT (Q (f (a+t*:v))-Q (P (a+t*:v)))<=C*NY (f (a+t*:v)-P (a+t*:v)).
  move=>/andP [_ ht].
  have /andP [htr hts] : (`|t|<r)&&(`|t|<s) by rewrite -lt_min.
  have hsmallP := (hsB t hts).2; rewrite heP in hsmallP.
  exact (hLip _ _ (hrB t htr).2 hsmallP).
have hmin : 0<Num.min r s by rewrite lt_min hr hs.
exact (norm_little_o_power_domination hNY (ltW hC) hmin hbound
  (norm_jet_line_little_o hNX hNY hZ ha hf hP v)).
Qed.

(** Source for [norm_composition_jet_radial_remainder]: the
    composition-of-jets limit displayed in Federer 3.1.11,
    p. 222, along every fixed source line. The separate error
    estimates establish the coefficient comparison used below. *)
Theorem norm_composition_jet_radial_remainder v :
  norm_little_o_power NT
    (fun t=>g (f (a+t*:v))-Q (P (a+t*:v))) k.
Proof.
have hh := norm_little_o_power_add hNT
  (norm_outer_jet_pullback_remainder v) (norm_inner_jet_polynomial_remainder v).
move=>e he; have [d [hd hbnd]] := hh e he.
exists d; split=> // t ht.
have h := hbnd t ht; by rewrite subrKA in h.
Qed.
End CompositionRemainder.
