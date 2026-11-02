(** Federer (1969), 3.1.11, p. 221:
    restricting the Taylor polynomial to a line
    turns its homogeneous terms into scalar powers. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring lra.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP
  MultilinearFamilyAlgebra NormTaylorRemainderBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [continuous_multilinear_diagonal_scale]:
    simultaneous scaling of all arguments yields
    the kth scalar power, supporting the
    linewise Taylor comparison in Federer 3.1.11,
    p. 221, using multilinearity from p. 219. *)
Lemma continuous_multilinear_diagonal_scale (R : realType) k
    (X Y Z : lmodType R) (NX : X->R) (NY : Y->R)
    (ev : {ffun 'I_k->X}->Hom Z Y) (ZN : Z->R)
    (hZ : is_continuous_multilinear_space NX NY ev ZN) z t v :
  ev [ffun _ : 'I_k=>t*:v] z=t^+k*:ev [ffun _ : 'I_k=>v] z.
Proof.
have he : [ffun _ : 'I_k=>t*:v]=[ffun i : 'I_k=>t*:[ffun _ : 'I_k=>v] i].
  by apply/ffunP=>i; rewrite !ffunE.
rewrite he (multilinear_family_scale_all (continuous_multilinear_evaluation hZ z))
  prodr_const card_ord; by [].
Qed.

(** Source for [norm_taylor_value_on_line]:
    the polynomial in Federer 3.1.11,
    p. 221, along a+t v
    has coefficient D^i f(a)(v,...,v)/i!
    for the scalar power t^i. *)
Lemma norm_taylor_value_on_line (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (D : forall i, X->Z i) a v t k :
  norm_taylor_value ev D a (t*:v) k=
    \sum_(i<k.+1) t^+i*:(((i`!)%:R)^-1*:@ev i [ffun _ : 'I_i=>v] (D i a)).
Proof.
rewrite /norm_taylor_value; apply: eq_bigr=>i _.
rewrite (continuous_multilinear_diagonal_scale (@hZ i)) !scalerA.
by rewrite mulrC.
Qed.

(** Source for [norm_scalar_line_small_increments]:
    small scalar increments give small vector
    increments along every fixed direction, supporting
    Federer 3.1.11, p. 221.
    The choice also covers the zero direction. *)
Lemma norm_scalar_line_small_increments (R : realType)
    (X : lmodType R) (N : X->R) (hN : is_real_norm N) v r :
  0<r -> exists d : R, 0<d /\ forall t, `|t|<d -> N (t*:v)<r.
Proof.
move=>hr.
have hn := real_seminorm_nonnegative hN.1 v.
have hp : 0<N v+1 by lra.
exists (r/(N v+1)); split; first by rewrite divr_gt0.
move=>t ht; rewrite (real_seminorm_scale hN.1).
have hle : N v<=N v+1 by lra.
apply: le_lt_trans (ler_wpM2l (normr_ge0 t) hle) _.
by move:ht; rewrite ltr_pdivlMr.
Qed.
