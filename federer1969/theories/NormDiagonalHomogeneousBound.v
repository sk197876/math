(** Federer (1969), 3.1.24, p. 238: homogeneity
    transfers the diagonal unit-ball bound to arbitrary increments. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP RealNormNormalization ContinuousMultilinearUP NormTaylorLineValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [normalized_diagonal_homogeneous_bound]: supporting
    the implication (2) to (3) in Federer 3.1.24,
    p. 238. The normalized m-linear diagonal value
    at v is bounded by M|v|^m once it is bounded
    by M on the closed unit ball. Zero increments and
    degree zero are included by the norm normalization laws. *)
Lemma normalized_diagonal_homogeneous_bound (R:realType) m (X Y Z:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (ev:{ffun 'I_m->X}->Hom Z Y) (ZN:Z->R)
    (hZ:is_continuous_multilinear_space NX NY ev ZN) z M :
  (forall v,NX v<=1 -> NY ((m`!)%:R^-1 *: ev [ffun i=>v] z)<=M) ->
  forall v,NY ((m`!)%:R^-1 *: ev [ffun i=>v] z)<=M*(NX v)^+m.
Proof.
move=>hb v.
pose u:=@real_norm_normalize R X NX v.
have hu:NX u<=1:=@real_norm_normalize_unit R X NX hNX.1 v.
have hre:NX v*:u=v:=@real_norm_normalize_reconstruct R X NX hNX.2 v.
have hargs:[ffun i:'I_m=>v]=[ffun i:'I_m=>NX v*:u].
  apply/ffunP=>i; by rewrite !ffunE hre.
rewrite hargs (@continuous_multilinear_diagonal_scale R m X Y Z NX NY ev ZN hZ z (NX v) u).
rewrite scalerA [(m`!)%:R^-1*(NX v)^+m]mulrC -scalerA.
have hp:0<=(NX v)^+m:=exprn_ge0 m (real_seminorm_nonnegative hNX.1 v).
rewrite (real_seminorm_scale hNY.1) (ger0_norm hp).
rewrite [M*(NX v)^+m]mulrC; exact (ler_wpM2l hp (hb u hu)).
Qed.
