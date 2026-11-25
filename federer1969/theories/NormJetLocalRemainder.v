(** Federer (1969), 3.1.11, pp. 221–222: the local Taylor
    remainder at one base point, with arbitrary small vector increments.
    This is the singleton case of the compact-uniform jet estimate. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets topology.
From Federer Require Import Hom RealNormUP NormMetric PolynomialFunctions
  ContinuousMultilinearUP NormClassHigherUP NormJetUP NormJetCompactRemainder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_jet_local_remainder]: the Taylor remainder
    at a fixed base point is negligible relative to the kth power
    of the increment, Federer 3.1.11, p. 221. Dropping the factorial
    factor gives the supporting estimate used in the composition
    calculation on p. 222. The bound includes the zero increment. *)
Theorem norm_jet_local_remainder (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A : set X) (f : X->Y) k a (P : PolynomialFunction X Y) :
  A a -> norm_class_higher NX NY ev ZN A f k ->
  is_norm_jet_polynomial NX ev ZN A f k a P ->
  forall e : R, 0<e -> exists d : R, 0<d /\
    forall v, NX v<d -> A (a+v) /\
      NY (f (a+v)-P (a+v))<=e*(NX v)^+k.
Proof.
move=>ha hf hP e he.
have hK : compact [set x : real_norm_metric_space hNX | x=a].
  exact: compact_set1.
have hKA : [set a] `<=` A by move=>x ->; exact ha.
have [d [hd hb]] := @norm_jet_compact_uniform_remainder R X Y NX NY hNX hNY
  Z ev ZN hZ A [set a] f k hf hK hKA e he.
exists d; split=> // v hv.
have [hav hrem] := hb a v P (erefl a) hv hP.
split; first exact hav.
have hfac : (1:R)<=(k`!)%:R by rewrite ler1n fact_gt0.
have hh := ler_wpM2l (real_seminorm_nonnegative hNY.1 (f (a+v)-P (a+v))) hfac.
rewrite mulr1 in hh; exact (le_trans hh hrem).
Qed.
