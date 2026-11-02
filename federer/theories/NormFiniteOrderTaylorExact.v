(** Federer (1969), 3.1.11, p. 221:
    a vanishing differential of order k+1 makes
    the Taylor polynomial of order k exact.
    This supports the identification of differentiated jets. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP
  ContinuousMultilinearNorm NormHigherDifferentialUP NormHigherDifferentialUnique
  NormClassHigherUP NormClassHigherFields NormTaylorRemainderBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_finite_order_taylor_exact]:
    the vanishing of the derivative above the
    polynomial degree makes Taylor's formula exact,
    Federer 3.1.11, p. 221. The proof
    uses the Taylor remainder theorem and needs
    no completeness of the target normed space. *)
Theorem norm_finite_order_taylor_exact (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (f : X->Y) k :
  norm_class_higher NX NY ev ZN (fun _=>True) f k.+1 ->
  (forall x, has_norm_higher_differential NX ev ZN (fun _=>True) f k.+1 x 0) ->
  exists D : forall i, X->Z i,
    (forall i, (i<=k)%N -> forall x,
      has_norm_higher_differential NX ev ZN (fun _=>True) f i x (D i x)) /\
    forall a v, f (a+v)=norm_taylor_value ev D a v k.
Proof.
move=>hc hzero.
have [D [hD hcont]] := norm_class_higher_fields hNX hNY hZ hc.
have hDz x : D k.+1 x= 0.
  exact (norm_higher_differential_unique hNX hNY hZ
    (hD k.+1 (leqnn _) x I) (hzero x)).
exists D; split.
- move=>i hi x; apply: hD=>//.
  exact: leq_trans hi (leqnSn k).
- move=>a v.
  have hseg t (_ : (0:R)<=t<=1) : True := I.
  have hosc t (_ : (0:R)<=t<=1) :
      @ZN k.+1 (D k.+1 (a+t*:v)-D k.+1 a)<=0.
    rewrite !hDz subrr.
    by rewrite (real_seminorm_zero
      (continuous_multilinear_norm_is_norm hNY (@hZ k.+1)).1).
  have hb := @norm_taylor_remainder_oscillation_bound R X Y NX NY hNX hNY
    Z ev ZN hZ (fun _=>True) f D a v k 0 hD
    (hcont k.+1 (leqnn _)) hseg hosc.
  rewrite mul0r mul0r in hb.
  have hT : norm_taylor_value ev D a v k.+1=norm_taylor_value ev D a v k.
    by rewrite /norm_taylor_value big_ord_recr /= hDz linear0 scaler0 addr0.
  rewrite hT in hb.
  have hz : NY (f (a+v)-norm_taylor_value ev D a v k)= 0.
    apply/eqP; rewrite eq_le; apply/andP; split=>//.
    exact: real_seminorm_nonnegative hNY.1 _.
  have he : f (a+v)-norm_taylor_value ev D a v k= 0 := hNY.2 _ hz.
  exact: subr0_eq he.
Qed.
