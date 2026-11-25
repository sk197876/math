(** Federer (1969), 3.4.5, pp. 318–321: actual
    finite jet agreement gives the uniform small-increment
    Taylor remainder of 3.1.11, p. 221. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets lra.
From Federer Require Import Hom RealNormUP PolynomialFunctions ContinuousMultilinearUP
  NormHigherDifferentialUP NormClassHigherUP NormClassHigherFields NormJetUP NormJetSealed
  NormJetLocalRemainder NormFiniteJetAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section UniformRemainder.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable Z:nat->lmodType R.
Variable ev:forall i,{ffun 'I_i->X}->Hom (Z i) Y.
Variable NZ:forall i,Z i->R.
Hypothesis hZ:forall i,is_continuous_multilinear_space NX NY (@ev i) (@NZ i).

(** Source for [norm_finite_jet_uniform_remainder]: equality
    of the actual kth jets implies an arbitrarily
    small order-k remainder bound on all sufficiently small
    vector increments, supporting 3.4.5, pp. 318–321.
    The original domains and zero increments are retained. *)
Theorem norm_finite_jet_uniform_remainder (A B:set X) (f g:X->Y) k a:
  A a ->B a ->
  norm_class_higher NX NY ev NZ A f k ->
  norm_class_higher NX NY ev NZ B g k ->
  norm_finite_jet_agreement NX ev NZ A B f g k a ->
  forall epsilon:R,0<epsilon ->exists r:R,0<r /\forall h,NX h<r ->
    NY (f (a+h)-g (a+h))<=epsilon*(NX h)^+k.
Proof.
move=>ha hb hf hg hAgree epsilon hEpsilon.
have [D [hD hContinuous]]:=norm_class_higher_fields hNX hNY hZ hf.
pose z:=D k a.
pose hz:=hD k (leqnn k) a ha.
pose P:=@NormJet.value R X Y NX NY hNX hNY Z ev NZ hZ A f k a z hz.
have hP:=@NormJet.laws R X Y NX NY hNX hNY Z ev NZ hZ A f k a z hz.
have hPG:is_norm_jet_polynomial NX ev NZ B g k a P.
  constructor;first exact:(norm_jet_polynomial_degree hP).
  have [E [hE hExpansion]]:=norm_jet_polynomial_expansion hP.
  exists E;split;last exact:hExpansion.
  move=>i hi;exact:(hAgree i hi (E i)).1 (hE i hi).
have hHalf:0<epsilon/2 by rewrite divr_gt0 // ltr0n.
have [r [hr hF]]:=norm_jet_local_remainder hNX hNY hZ ha hf hP hHalf.
have [s [hs hG]]:=norm_jet_local_remainder hNX hNY hZ hb hg hPG hHalf.
exists (Num.min r s);split;first by rewrite lt_min hr hs.
move=>h hh;have /andP [hR hS]:(NX h<r)&&(NX h<s) by rewrite -lt_min.
have hIdentity:f (a+h)-g (a+h)=(f (a+h)-P (a+h)) + -(g (a+h)-P (a+h)).
  by rewrite opprB addrA subrK.
rewrite hIdentity.
apply:(le_trans (real_seminorm_triangle hNY.1 _ _) _).
rewrite (real_seminorm_negate hNY.1).
have hSum:=lerD (hF h hR).2 (hG h hS).2.
have hHalfSum:epsilon/2+epsilon/2=epsilon by lra.
by rewrite -mulrDl hHalfSum in hSum.
Qed.
End UniformRemainder.
