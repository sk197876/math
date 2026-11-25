(** Federer (1969), 1.7.2, pp. 28-29: duality of the two norms. We first
    prove the norm is an attained upper bound; a separate real-completeness
    interface gives the printed supremum formula. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities
  InnerNormalization InnerPolarity OneFormLinear Hom LinearBasis
  AlternatingCoordinates Bilinear.
From Federer Require Import InnerDual InnerPolaritySurjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section DualNorm.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Local Notation F := (A_m V R^o 1).
Local Notation N := (inner_norm hB).
Local Notation D := (inner_dual_norm hB he).

(** Source for [inner_dual_evaluation_bound]: Federer 1.7.2, pp. 28-29,
    supporting Cauchy bound for evaluation against a one-covector, in the
    stronger absolute-value form. *)
Lemma inner_dual_evaluation_bound (a : F) x : `|one_hom a x| <= N x * D a.
Proof.
have [y <-] := @inner_polarity_surjective R V B hB n e he a.
rewrite inner_dual_norm_polarity one_homE inner_polarityE.
exact: inner_cauchy.
Qed.

(** Source for [inner_dual_unit_bound]: Federer 1.7.2,
    p. 28, every evaluation on the primal unit ball is at most the
    dual norm, the upper-bound half of the printed supremum formula. *)
Lemma inner_dual_unit_bound (a : F) x : N x <= 1 -> one_hom a x <= D a.
Proof.
move=> hx.
have hn : 0 <= D a := inner_norm_nonnegative _ _.
have hc := le_trans (ler_norm (one_hom a x)) (inner_dual_evaluation_bound a x).
apply: (le_trans hc).
have hm := ler_wpM2r hn hx.
by rewrite mul1r in hm.
Qed.

(** Source for [inner_dual_norm_attained]: Federer 1.7.2,
    pp. 28-29, supporting attainment of the supremum: normalise the
    vector corresponding to the covector. For the zero covector, use
    the zero vector; this includes dimension zero. *)
Theorem inner_dual_norm_attained (a : F) :
  exists x, N x <= 1 /\ one_hom a x = D a.
Proof.
have [y <-] := @inner_polarity_surjective R V B hB n e he a.
rewrite inner_dual_norm_polarity.
have [->|hy] := eqVneq y 0.
- exists 0; rewrite inner_norm0; split; first exact: ler01.
  by rewrite one_homE inner_polarityE (bil0l (inner_bilinear hB)).
- exists (inner_normalize hB y); split.
  + by rewrite inner_normalize_norm //.
  + rewrite one_homE inner_polarityE /inner_normalize
      (bilZl (inner_bilinear hB)) -(inner_norm_sqr hB y).
    change ((N y)^-1 * (N y)^+2 = N y).
    by rewrite expr2 mulrA mulVf ?mul1r // inner_norm_eq0.
Qed.
End DualNorm.
