(** Federer (1969), 3.1.11, p. 221:
    the compact-uniform remainder for every derivative
    of the Taylor jet, including the highest derivative.
    The comparison uses the actual derivative of
    the actual jet polynomial. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import Hom RealNormUP NormMetric PolynomialFunctions
  ContinuousMultilinearUP ContinuousMultilinearNorm NormHigherDifferentialUP
  NormHigherDifferentialUnique NormClassHigherUP NormClassHigherLaws
  NormClassHigherDerivative NormJetUP NormJetRestriction
  NormJetDifferentiation NormJetCompactRemainder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_derivative_jet_compact_uniform_remainder]:
    for a function of class p+q,
    the difference D^p f(x)-D^p F_a(x),
    multiplied by q! and divided by |x-a|^q,
    tends to zero uniformly for a in
    compact subsets of its domain, Federer
    3.1.11, p. 221. The bound
    is written without division and includes q= 0. *)
Theorem norm_derivative_jet_compact_uniform_remainder (R : realType) p q
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
    (A K : set X) (f : X->Y) (H : X->Z p) :
  norm_class_higher NX NY ez ZN A f (p+q)%N ->
  (forall x z, has_norm_higher_differential NX ez ZN A f p x z -> H x=z) ->
  compact [set x : real_norm_metric_space hNX | K x] ->
  K `<=` A ->
  forall e : R, 0<e -> exists d : R, 0<d /\
    forall a v (P : PolynomialFunction X Y) (z : Z p),
      K a -> NX v<d ->
      is_norm_jet_polynomial NX ez ZN A f (p+q)%N a P ->
      has_norm_higher_differential NX ez ZN (fun _=>True) P p (a+v) z ->
      A (a+v) /\ @ZN p (H (a+v)-z)*((q`!)%:R)<=e*(NX v)^+q.
Proof.
move=>hc hH hK hKA e he.
have hNp := continuous_multilinear_norm_is_norm hNY (@hZ p).
have hple : (p<=p+q)%N := leq_addr _ _.
have [_ [G [hG hGc]]] := norm_class_higher_lower hNX hNY hZ hple hc.
have hfield x (hx : A x) :
    has_norm_higher_differential NX ez ZN A f p x (H x).
  by rewrite (hH x (G x) (hG x hx)); exact: hG.
have hHc := @norm_class_higher_derivative_field R p q X Y NX NY hNX hNY
  Z ez ZN hZ W ew WN hW A f H hc hfield.
have [d [hd hb]] := @norm_jet_compact_uniform_remainder R X (Z p) NX (@ZN p)
  hNX hNp W ew WN hW A K H q hHc hK hKA e he.
exists d; split=>// a v P z ha hv hP hz.
have [Q [hDQ hQ]] := @norm_jet_differentiation R p q X Y NX NY hNX hNY
  Z ez ZN hZ W ew WN hW A f a P H hP hH.
pose B x := exists w, has_norm_higher_differential NX ez ZN A f p x w.
have hAB x (hx : A x) : B x by exists (H x); exact: hfield.
have hopen x (hx : A x) := (hc.1 x hx).1.
have hQA := (@norm_jet_open_restriction R X (Z p) NX (@ZN p) hNX hNp
  W ew WN hW B A H q a Q hAB hopen (hKA a ha)).1 hQ.
have [hav hbound] := hb a v Q ha hv hQA.
have heq := norm_higher_differential_unique hNX hNY hZ (hDQ (a+v)) hz.
split; first exact hav; by rewrite -heq.
Qed.
