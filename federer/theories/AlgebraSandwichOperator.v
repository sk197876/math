(** Federer (1969), 3.1.11, p. 220:
    the bilinear operator-valued map (v,w) to
    h to v h w. Its diagonal gives,
    with a minus sign, the derivative of inversion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals ring.
From Federer Require Import Hom TensorUP Bilinear AlgebraUP RealNormUP
  NormDifferentialUP NormOperatorNormUP ContinuousOperatorUP
  ContinuousMultilinearUP ContinuousMultilinearOne NormBoundedBilinearUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [algebra_sandwich_linear]: the
    map h to v h w is linear,
    supporting the inverse differential in Federer
    3.1.11, p. 220. *)
Lemma algebra_sandwich_linear (R : realType) (A : algebra R) (v w : A) :
  linear (fun h=>alg_mul A v (alg_mul A h w)).
Proof.
move=> c h k.
rewrite (alg_bilinear A).1 (alg_bilinear A).2.
by [].
Qed.

(** Source for [algebra_sandwich_operator_exists]:
    the two inverse factors in the derivative
    of inversion give a bounded bilinear map
    into the continuous one-linear space, supporting
    Federer 3.1.11, p. 220.
    Only abstract operator representation and norm
    laws are used. *)
Theorem algebra_sandwich_operator_exists (R : realType)
    (A : algebra R) (N : A->R) (hN : is_real_norm N)
    (hM : forall x y, N (alg_mul A x y)<=N x*N y)
    (P : lmodType R) (ep : {ffun 'I_1->A}->Hom P A) (PN : P->R)
    (hP : is_continuous_multilinear_space N N ep PN) :
  exists B : A->A->P,
    norm_bounded_bilinear N N PN B /\
    forall v w h, ep [ffun _ : 'I_1=>h] (B v w)=alg_mul A v (alg_mul A h w).
Proof.
pose Op := @continuous_multilinear_one_evaluation R A A P N N ep PN hP.
have hop := continuous_multilinear_one_operator_space hP.
pose L v w := @HomMap R A A (fun h=>alg_mul A v (alg_mul A h w))
  (introT (asboolP _) (algebra_sandwich_linear v w)).
have hbound v w h : N (L v w h)<=(N v*N w)*N h.
  change (is_true (N (alg_mul A v (alg_mul A h w))<=(N v*N w)*N h)).
  apply: le_trans (hM _ _) _.
  have hh := ler_wpM2l (real_seminorm_nonnegative hN.1 v) (hM h w).
  by rewrite [N h*N w]mulrC mulrA in hh.
have hb v w : norm_bounded_linear N N (L v w).
  exists (N v*N w); split.
  - exact: mulr_ge0 (real_seminorm_nonnegative hN.1 v)
      (real_seminorm_nonnegative hN.1 w).
  - exact: hbound.
have hex (vw : A*A) := continuous_operator_surjective hop (hb vw.1 vw.2).
have [b hbE] := choice hex.
pose B v w := b (v,w).
have hBE v w : Op (B v w)=L v w := hbE (v,w).
have hE v w h : Op (B v w) h=alg_mul A v (alg_mul A h w).
  by rewrite hBE.
exists B; split; last exact hE.
split.
- split.
  + move=> w c v v'; apply: (continuous_operator_injective hop); apply: hom_ext=>h.
    rewrite (hom_linear Op) hom_addE hom_scaleE !hE.
    exact: (alg_bilinear A).1 (alg_mul A h w) c v v'.
  + move=> v c w w'; apply: (continuous_operator_injective hop); apply: hom_ext=>h.
    rewrite (hom_linear Op) hom_addE hom_scaleE !hE.
    by rewrite (alg_bilinear A).2 (alg_bilinear A).2.
- exists 1; split; first exact: ler01.
  move=> v w; rewrite mul1r.
  apply: (norm_operator_least (continuous_operator_norm_laws hop (B v w))
    (mulr_ge0 (real_seminorm_nonnegative hN.1 v)
      (real_seminorm_nonnegative hN.1 w)))=>h.
  rewrite hBE; exact: hbound.
Qed.
