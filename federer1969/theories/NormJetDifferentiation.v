(** Federer (1969), 3.1.11, p. 221:
    D^p of the (p+q)-jet is the
    q-jet of the actual pth differential.
    Differentiability at the base point suffices;
    a class-(p+q) neighbourhood is not assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  PolynomialFunctions PolynomialRepresentations
  ContinuousMultilinearUP ContinuousMultilinearNorm
  MultilinearArguments NormHigherDifferentialUP NormHigherDifferentialUnique
  NormHigherDifferentialLocal NormHigherDifferentialIterated
  PolynomialHigherDifferentials PolynomialDifferentialDegree
  NormJetUP NormJet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_jet_differentiation]:
    D^p F_a is the q-jet of
    D^p f at a when F_a is
    the (p+q)-jet of f, Federer
    3.1.11, p. 221. The statement
    refers to the actual domain of D^p f
    and to a polynomial with the exact
    values of D^p F_a on all X. *)
Theorem norm_jet_differentiation (R : realType) p q
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ez : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ez i) (@ZN i))
    (W : nat->lmodType R)
    (ew : forall i, {ffun 'I_i->X}->Hom (W i) (Z p))
    (WN : forall i, W i->R)
    (hW : forall i, is_continuous_multilinear_space NX (@ZN p) (@ew i) (@WN i))
    (A : X->Prop) (f : X->Y) a (P : PolynomialFunction X Y)
    (H : X->Z p) :
  is_norm_jet_polynomial NX ez ZN A f (p+q)%N a P ->
  (forall x z, has_norm_higher_differential NX ez ZN A f p x z -> H x=z) ->
  exists Q : PolynomialFunction X (Z p),
    (forall x, has_norm_higher_differential NX ez ZN (fun _=>True) P p x (Q x)) /\
    is_norm_jet_polynomial NX ew WN
      (fun x=>exists z, has_norm_higher_differential NX ez ZN A f p x z)
      H q a Q.
Proof.
move=>hP hH.
have hNp := continuous_multilinear_norm_is_norm hNY (@hZ p).
have hopen x (_ : True) : norm_domain_interior NX (fun _=>True) x.
  exists 1; split; first exact: ltr01; by move=>v hv.
have hbound i (_ : (i<(polynomial_degree P).+1)%N) :=
  norm_jet_coefficients_bounded hNX hNY hZ hP i.
have [D [hDe hD]] := @polynomial_higher_differential_fields_exist R X Y NX NY
  hNX hNY Z ez ZN hZ (fun _=>True) hopen P hbound.
pose G := D p.
have hG x : has_norm_higher_differential NX ez ZN (fun _=>True) P p x (G x).
  exact: hD p x I.
have [Q [hQ heQ]] := @polynomial_differential_polynomial_exists R p q X Y NX NY
  hNX hNY Z ez ZN hZ W ew WN hW P hbound G hG a
  (norm_jet_polynomial_degree hP).
exists Q; split.
- move=>x; rewrite heQ; exact: hG.
- constructor; first exact: norm_jet_polynomial_degree hQ.
  have [E [hE hQe]] := norm_jet_polynomial_expansion hQ.
  exists E; split; last exact hQe.
  have [F [hF hPe]] := norm_jet_polynomial_expansion hP.
  move=>i hi.
  have hpi : (p+i<=p+q)%N by rewrite leq_add2l.
  pose z := F (p+i)%N.
  have hf := hF (p+i)%N hpi.
  have hp := norm_jet_differential_at_base hNX hNY hZ hP hpi hf.
  have [w [hw hwe]] := (@norm_higher_differential_iterated R p i X Y NX NY
    hNX hNY Z ez ZN hZ W ew WN hW A f H a z hH).1 hf.
  have hrep x v :
      has_norm_higher_differential NX ez ZN (fun _=>True) P p x v -> G x=v.
    move=>hz; exact (norm_higher_differential_unique hNX hNY hZ (hG x) hz).
  have [wP [hwP hwPe]] := (@norm_higher_differential_iterated R p i X Y NX NY
    hNX hNY Z ez ZN hZ W ew WN hW (fun _=>True) P G a z hrep).1 hp.
  have hww : wP=w.
    apply: (continuous_multilinear_extensional (@hW i))=>v.
    apply: (continuous_multilinear_extensional (@hZ p))=>u.
    by rewrite hwPe hwe.
  pose B x := exists v, has_norm_higher_differential NX ez ZN (fun _=>True) P p x v.
  have hB x (_ : True) : B x by exists (G x); exact: hG.
  have hr := @norm_higher_differential_open_restriction R X (Z p) NX (@ZN p)
    hNX hNp W ew WN hW i B (fun _=>True) G hB hopen a I wP.
  have hwA := hr.1 hwP.
  have he : wP=E i := norm_higher_differential_unique hNX hNp hW hwA (hE i hi).
  by rewrite -he hww.
Qed.
