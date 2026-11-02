(** Federer (1969), 3.1.11, p. 221:
    the linewise asymptotic polynomial determines
    every higher differential through its stated order. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP
  FiniteArgumentPermutation ContinuousMultilinearDiagonalUniqueness
  NormHigherDifferentialUP NormHigherDifferentialSymmetry
  NormClassHigherUP NormClassHigherFields NormTaylorRemainderBound
  NormTaylorLineValues NormTaylorLineRemainder NormLittleOPower
  FinitePowerAsymptoticUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_higher_differential_from_radial_expansion]:
    Federer 3.1.11, p. 221, the
    corollary identifying D^i f(a) with the
    coefficients of a linewise order-k approximation.
    Coefficients of a polynomial of degree M<=k
    are extended by zero above M.
    The class-k hypothesis is retained exactly;
    pointwise k-fold differentiability alone is not
    substituted for it. *)
Theorem norm_higher_differential_from_radial_expansion (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A : X->Prop) (f : X->Y) k a (phi : forall i, Z i) :
  A a ->
  norm_class_higher NX NY ev ZN A f k ->
  (forall i, (i<=k)%N -> forall s u,
    @ev i (finite_argument_permutation s u) (phi i)=@ev i u (phi i)) ->
  (forall v, norm_little_o_power NY
    (fun t=>f (a+t*:v)-norm_taylor_value ev (fun i _=>phi i) a (t*:v) k) k) ->
  forall i, (i<=k)%N ->
    has_norm_higher_differential NX ev ZN A f i a (phi i).
Proof.
move=>ha hf hsym happrox.
have [D [hD hc]] := norm_class_higher_fields hNX hNY hZ hf.
move=>i hi.
have hactual := hD i hi a ha.
have he : D i a=phi i.
  apply: (continuous_multilinear_symmetric_diagonal_injective (@hZ i)).
  - exact (@norm_higher_differential_symmetric R X Y NX NY hNX hNY Z ev ZN hZ A f i a (D i a) hactual).
  - exact: hsym i hi.
  - move=>v.
    pose c j := ((j`!)%:R)^-1*:@ev j [ffun _ : 'I_j=>v] (D j a).
    pose d j := ((j`!)%:R)^-1*:@ev j [ffun _ : 'I_j=>v] (phi j).
    have hcO : norm_little_o_power NY
        (fun t=>f (a+t*:v)-\sum_(j<k.+1) t^+j*:c j) k.
      have hh := @norm_taylor_line_little_o_fields R X Y NX NY hNX hNY
        Z ev ZN hZ A f D k a v ha hf.1 hD (hc k (leqnn _)).
      move=>e heps; have [r [hr hb]] := hh e heps.
      exists r; split=> // t ht.
      have h := hb t ht.
      by rewrite (norm_taylor_value_on_line hZ) in h.
    have hdO : norm_little_o_power NY
        (fun t=>f (a+t*:v)-\sum_(j<k.+1) t^+j*:d j) k.
      move=>e heps; have [r [hr hb]] := happrox v e heps.
      exists r; split=> // t ht.
      have h := hb t ht.
      by rewrite (norm_taylor_value_on_line hZ) in h.
    have hii : (i<k.+1)%N by rewrite ltnS.
    have hcoeff := @finite_power_asymptotic_coefficients_unique R Y NY hNY
      k k.+1 (fun t=>f (a+t*:v)) c d (leqnn _) hcO hdO i hii.
    have hp : (0:R)<(i`!)%:R by rewrite ltr0n fact_gt0.
    have hn : ((i`!)%:R : R)!=0 by rewrite gt_eqF.
    have hh := congr1 (fun y : Y=>((i`!)%:R : R)*:y) hcoeff.
    by rewrite /c /d !scalerA mulfV // !scale1r in hh.
by rewrite -he.
Qed.
