(** Supporting Federer (1969), 3.4.8(5), p. 328:
    finite prefixes retain actual derivative arithmetic,
    have a compatible norm, and are finite dimensional
    when the original source is finite dimensional.
    Every proof uses the existing opaque product laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP LinearBasis NormedFamilyUP NormedFamilySealed
  NormedFamilyLaws NormedFamilyFiniteBasis ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearNorm FiniteMultilinearCoordinates AnalyticGermUP AnalyticGermRing AnalyticGermSealed AnalyticGermJetsSealed
  AnalyticGermJetArithmetic AnalyticGermJetZeroNegate AnalyticGermRepresentatives
  WeierstrassScalarGermArithmetic AnalyticFiniteJetsUP AnalyticFiniteJetsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Laws.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Variable hNX:is_real_norm NX.
Variable m:nat.
Local Notation Z:=(fun i:'I_m=>@ContinuousMultilinear.space R i X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R)).
Local Notation N:=(fun i:'I_m=>@ContinuousMultilinear.norm R i X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R)).
Local Notation P:=(@analytic_finite_jet_space R X NX hNX m).

(** Source for [analytic_finite_jet_norm_laws]: the
    finite sum of actual derivative norms is a norm,
    supporting 3.4.8(5), p. 328, with the product
    of 3.1.1(4), p. 210. *)
Lemma analytic_finite_jet_norm_laws:is_real_norm (@analytic_finite_jet_norm R X NX hNX m).
Proof.
apply:(@normed_family_is_norm R m Z N _ P
  (@analytic_finite_jet_coordinate R X NX hNX m) (@analytic_finite_jet_norm R X NX hNX m)
  (@NormedFamily.laws R m Z N))=>i.
exact:(continuous_multilinear_norm_is_norm (@scalar_absolute_value_norm R)
  (@ContinuousMultilinear.laws R i X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R))).
Qed.

(** Source for [analytic_finite_jet_basis_exists]: finite
    source dimension gives finite-dimensional actual derivative
    prefixes, supporting 3.4.8(5), p. 328, from
    1.10.5, p. 47, and 1.6.1, p. 23. *)
Lemma analytic_finite_jet_basis_exists n (b:'I_n->X) (hb:is_basis b):
  exists q (e:'I_q->P),is_basis e.
Proof.
apply:(@normed_family_finite_basis_exists R m Z N P
  (@analytic_finite_jet_coordinate R X NX hNX m) (@analytic_finite_jet_norm R X NX hNX m)
  (@NormedFamily.laws R m Z N))=>i.
have [q [e [he _]]]:=@finite_scalar_multilinear_basis_exists R X NX hNX n b hb i.
by exists q,e.
Qed.

Variable a:X.
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX a)].
Local Notation f:=(@AnalyticFiniteJets.map R X NX hNX m a).

(** Source for [analytic_finite_jet_zero]: the original
    zero germ has zero finite derivative prefix,
    supporting 3.4.8(5), p. 328, from 3.4.5, p. 319. *)
Lemma analytic_finite_jet_zero:f 0 = 0.
Proof.
apply:(normed_family_extensional (@NormedFamily.laws R m Z N))=>i.
rewrite (@AnalyticFiniteJets.laws R X NX hNX m a 0 i) linear0.
exact:(@analytic_germ_jet_zero R X NX hNX a i).
Qed.

(** Source for [analytic_finite_jet_add]: the actual
    finite derivative map preserves germ addition,
    supporting the same original derivative assertions. *)
Lemma analytic_finite_jet_add (alpha beta:G):f (alpha+beta) = f alpha+f beta.
Proof.
apply:(normed_family_extensional (@NormedFamily.laws R m Z N))=>i.
rewrite linearD /= !(@AnalyticFiniteJets.laws R X NX hNX m a).
exact:(@analytic_germ_jet_add R X NX hNX a i alpha beta).
Qed.

(** Source for [analytic_finite_jet_scale]: multiplying by
    an original scalar constant scales the entire actual
    finite prefix, supporting 3.4.8(5), p. 328,
    from the derivative arithmetic of 3.4.5, p. 319. *)
Lemma analytic_finite_jet_scale (c:R) (alpha:G):
  f ((analytic_germ (@analytic_constant_representative R X NX hNX a c):G)*alpha) = c*:f alpha.
Proof.
apply:(normed_family_extensional (@NormedFamily.laws R m Z N))=>i.
rewrite linearZ /= !(@AnalyticFiniteJets.laws R X NX hNX m a).
exact:(@weierstrass_scalar_germ_jet R X NX hNX a i c alpha).
Qed.

(** Source for [analytic_finite_jet_equality]: equality
    of finite prefixes is exactly equality of every
    original derivative below the specified cutoff,
    supporting 3.4.8(5), p. 328, and the
    derivative coordinates of 3.4.5, p. 319. *)
Lemma analytic_finite_jet_equality (alpha beta:G):
  f alpha = f beta <->forall i,(i<m)%N ->
    @AnalyticGermJets.value R X NX hNX a i alpha = @AnalyticGermJets.value R X NX hNX a i beta.
Proof.
split.
- move=>hEqual i hi.
  have hValue:=congr1 (@analytic_finite_jet_coordinate R X NX hNX m (Ordinal hi)) hEqual.
  by rewrite !(@AnalyticFiniteJets.laws R X NX hNX m a) in hValue.
- move=>hEqual;apply:(normed_family_extensional (@NormedFamily.laws R m Z N))=>i.
  rewrite !(@AnalyticFiniteJets.laws R X NX hNX m a).
  exact:hEqual i (ltn_ord i).
Qed.
End Laws.
