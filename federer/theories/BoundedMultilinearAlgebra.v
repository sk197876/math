(** Federer (1969), 3.1.11, p. 219: the
    continuous multilinear maps form a vector space. These
    algebraic closure laws support its private existence witness. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP TensorFamilyUP FamilyUpdate ContinuousMultilinearUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Closure.
Variable R : realType.
Variable k : nat.
Variables X Y : lmodType R.
Variables NX : X->R.
Variable NY : Y->R.
Hypothesis hNY : is_real_norm NY.

(** Source for [norm_bounded_multilinear_zero]: zero belongs
    to the space in Federer 3.1.11, p. 219. *)
Lemma norm_bounded_multilinear_zero :
  norm_bounded_multilinear NX NY (fun _ : {ffun 'I_k->X}=>(0:Y)).
Proof.
split; first by move=> u i c v w; rewrite scaler0 addr0.
exists 0; split; first exact: lexx.
by move=> u; rewrite (real_seminorm_zero hNY.1) mul0r.
Qed.

(** Source for [norm_bounded_multilinear_add]: addition
    preserves continuous multilinearity, supporting the vector
    space in Federer 3.1.11, p. 219. *)
Lemma norm_bounded_multilinear_add (f g : {ffun 'I_k->X}->Y) :
  norm_bounded_multilinear NX NY f -> norm_bounded_multilinear NX NY g ->
  norm_bounded_multilinear NX NY (fun u=>f u+g u).
Proof.
move=> [hf [C [hC hb]]] [hg [D [hD hd]]]; split.
- move=> u i c v w; rewrite (hf u i) (hg u i) scalerDr.
  by rewrite addrACA.
- exists (C+D); split; first exact: addr_ge0 hC hD.
  move=> u; apply: le_trans (real_seminorm_triangle hNY.1 _ _) _.
  rewrite mulrDl; exact: lerD (hb u) (hd u).
Qed.

(** Source for [norm_bounded_multilinear_scale]: scalar
    multiplication preserves continuous multilinearity, supporting
    Federer 3.1.11, p. 219. *)
Lemma norm_bounded_multilinear_scale c (f : {ffun 'I_k->X}->Y) :
  norm_bounded_multilinear NX NY f ->
  norm_bounded_multilinear NX NY (fun u=>c*:f u).
Proof.
move=> [hf [C [hC hb]]]; split.
- move=> u i t v w; rewrite (hf u i) scalerDr !scalerA.
  by rewrite [c*t]mulrC.
- exists (`|c|*C); split; first exact: mulr_ge0 (normr_ge0 c) hC.
  move=> u; rewrite (real_seminorm_scale hNY.1) -mulrA.
  apply: ler_wpM2l; [exact: normr_ge0|exact: hb].
Qed.
End Closure.
