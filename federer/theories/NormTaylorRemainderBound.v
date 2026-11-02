(** Federer (1969), 3.1.11, p. 221:
    the Taylor remainder is bounded by the
    oscillation of the highest differential on
    the corrected segment a+t(x-a). *)
From mathcomp Require Import all_boot all_order all_algebra reals ring lra.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP
  ContinuousMultilinearNorm NormHigherDifferentialUP NormClassOneUP
  NormTaylorIntegral NormedStieltjesBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_taylor_value]:
    the Taylor polynomial evaluated at a+v,
    Federer 3.1.11, p. 221. The coefficient
    of degree i is the repeated-v evaluation
    of the actual ith differential, divided by i!. *)
Definition norm_taylor_value (R : realType) (X Y : lmodType R)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (D : forall i, X->Z i) a v k :=
  \sum_(i < k.+1) ((i`!)%:R)^-1*:
    (@ev i [ffun j : 'I_i=>v] (D i a)).

(** Source for [unit_complement_power_decreasing]:
    the integrator (1-t)^k in the Taylor
    formula of Federer 3.1.11, pp. 220–221,
    decreases on the unit interval. *)
Lemma unit_complement_power_decreasing (R : realType) k (s t : R) :
  0<=s -> s<=t -> t<= 1 -> (1-t)^+k<=(1-s)^+k.
Proof.
move=> hs hst ht.
have h0 : 0<= 1-t by rewrite subr_ge0.
have h1 : 0<= 1-s by rewrite subr_ge0; exact: le_trans hst ht.
have hle : 1-t<= 1-s by rewrite lerD2l lerN2.
exact (lerXn2r k h0 h1 hle).
Qed.

(** Source for [norm_taylor_remainder_oscillation_bound]:
    the Taylor integral yields the bound
    omega times norm(v)^k/k!, where omega bounds
    the change of D^k f on the segment.
    This is the estimate underlying the vanishing
    and compact-uniform remainders in Federer
    3.1.11, p. 221, with the segment
    corrected by erratum p. 4, book line 1. *)
Theorem norm_taylor_remainder_oscillation_bound (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A : X->Prop) (f : X->Y) (D : forall i, X->Z i)
    a v k (omega : R) :
  (forall i, (i<=k.+1)%N -> forall x, A x ->
    has_norm_higher_differential NX ev ZN A f i x (D i x)) ->
  norm_class_zero NX (@ZN k.+1) A (D k.+1) ->
  (forall t : R, 0<=t<= 1 -> A (a+t*:v)) ->
  (forall t : R, 0<=t<= 1 ->
    @ZN k.+1 (D k.+1 (a+t*:v)-D k.+1 a)<=omega) ->
  NY (f (a+v)-norm_taylor_value ev D a v k.+1)<=
    omega*(NX v)^+k.+1/((k.+1)`!)%:R.
Proof.
move=> hD hc hseg hw.
have hi := norm_taylor_integral_fields hNX hNY hZ hD hc hseg.
pose M := omega*(NX v)^+k.+1/((k.+1)`!)%:R.
have hnorm := continuous_multilinear_norm_is_norm hNY (@hZ k.+1).
have hfac : (0: R)<((k.+1)`!)%:R by rewrite ltr0n fact_gt0.
have hinv : 0<=(((k.+1)`!)%:R : R)^-1 by rewrite invr_ge0; exact: ltW hfac.
have hp : 0<=(NX v)^+k.+1 := exprn_ge0 _ (real_seminorm_nonnegative hNX.1 v).
have hb t (ht : 0<=t<= 1) :
    NY ((((k.+1)`!)%:R)^-1*:
      (@ev k.+1 [ffun j : 'I_k.+1=>v] (D k.+1 a)-
       @ev k.+1 [ffun j : 'I_k.+1=>v] (D k.+1 (a+t*:v))))<=M.
  rewrite (real_seminorm_scale hNY.1) (ger0_norm hinv) -linearB.
  have he := multilinear_operator_bound
    (continuous_multilinear_norm_laws (@hZ k.+1)
      (D k.+1 a-D k.+1 (a+t*:v))) [ffun j : 'I_k.+1=>v].
  have hprod : (\prod_(j<k.+1) NX ([ffun l : 'I_k.+1=>v] j))=(NX v)^+k.+1.
    under eq_bigr do rewrite ffunE.
    by rewrite prodr_const card_ord.
  rewrite hprod (real_seminorm_subtract hnorm.1) in he.
  have ho := ler_wpM2r hp (hw t ht).
  have hh := ler_wpM2l hinv (le_trans he ho).
  have heq : (((k.+1)`!)%:R)^-1*(omega*(NX v)^+k.+1)=M.
    by rewrite /M mulrC.
  by rewrite heq in hh.
have hbound := normed_stieltjes_integral_decreasing_bound hNY hi hb
  (@unit_complement_power_decreasing R k.+1).
rewrite subr0 expr1n subrr expr0n subr0 mulr1 in hbound.
exact hbound.
Qed.
