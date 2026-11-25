(** Federer (1969), 3.1.11, pp. 221–222:
    local bounds and linewise remainders for jets,
    used to multiply the Taylor approximations. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom RealNormUP NormClassOneUP PolynomialFunctions ContinuousMultilinearUP
  NormHigherDifferentialUnique NormClassHigherUP NormClassHigherFields
  NormTaylorRemainderBound NormTaylorLineValues NormTaylorLineRemainder
  NormLittleOPower NormJetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_class_zero_line_bounded]:
    the locally bounded factors used in
    the product-of-jets limit on Federer
    3.1.11, p. 222.
    The bound follows from continuity on
    the original open domain. *)
Lemma norm_class_zero_line_bounded (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (A : X->Prop) (f : X->Y) a v :
  A a -> norm_class_zero NX NY A f ->
  exists M r : R, 0<=M /\ 0<r /\
    forall t, `|t|<r -> A (a+t*:v) /\ NY (f (a+t*:v))<=M.
Proof.
move=>ha hf.
have [d [hd hA]] := (hf a ha).1.
have [s [hs hc]] := (hf a ha).2 1 ltr01.
have hmin : 0<Num.min d s by rewrite lt_min hd hs.
have [r [hr hb]] := norm_scalar_line_small_increments hNX v hmin.
exists (NY (f a)+1), r; split.
- exact: addr_ge0 (real_seminorm_nonnegative hNY.1 _) ler01.
split; first exact hr.
move=>t ht; have hsmall := hb t ht.
have /andP [htd hts] : (NX (t*:v)<d)&&(NX (t*:v)<s) by rewrite -lt_min.
have hat := hA (t*:v) htd.
split; first exact hat.
have hdiff := hc (t*:v) hat hts.
have he : f (a+t*:v)=(f (a+t*:v)-f a)+f a by rewrite subrK.
rewrite he; apply: le_trans (real_seminorm_triangle hNY.1 _ _) _.
by rewrite addrC; exact: lerD (lexx _) (ltW hdiff).
Qed.

(** Source for [norm_jet_line_little_o]:
    the kth jet differs from the
    class-k function by o(|t|^k)
    along every line, Federer 3.1.11,
    pp. 221–222. Degree zero is
    included through the continuity case. *)
Theorem norm_jet_line_little_o (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A : X->Prop) (f : X->Y) k a (P : PolynomialFunction X Y) :
  A a -> norm_class_higher NX NY ev ZN A f k ->
  is_norm_jet_polynomial NX ev ZN A f k a P ->
  forall v, norm_little_o_power NY (fun t=>f (a+t*:v)-P (a+t*:v)) k.
Proof.
move=>ha hf hP v.
have [D [hD hc]] := norm_class_higher_fields hNX hNY hZ hf.
have [E [hE hPe]] := norm_jet_polynomial_expansion hP.
have he t : P (a+t*:v)=norm_taylor_value ev D a (t*:v) k.
  rewrite hPe [a+t*:v-a]addrAC subrr add0r /norm_taylor_value.
  apply: eq_bigr=>i _.
  have hi : (i<=k)%N by move:(ltn_ord i); rewrite ltnS.
  have hz := norm_higher_differential_unique hNX hNY hZ (hE i hi) (hD i hi a ha).
  by rewrite hz.
have hh := @norm_taylor_line_little_o_fields R X Y NX NY hNX hNY
  Z ev ZN hZ A f D k a v ha hf.1 hD (hc k (leqnn k)).
move=>e heps; have [r [hr hb]] := hh e heps.
exists r; split=> // t ht; rewrite he; exact: hb.
Qed.
