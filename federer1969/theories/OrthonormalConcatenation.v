(** Federer (1969), 1.7.5, p. 32: the equality case for two simple factors.
    Supporting orthogonality of concatenated orthonormal families. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm OrthonormalFamilies
  ConcatenatedFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Concatenation.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variables p q : nat.
Variables (e : 'I_p -> V) (f : 'I_q -> V).
Hypotheses (he : orthonormal_family B e) (hf : orthonormal_family B f).

(** Source for [orthonormal_concatenation_unit]: Federer
    1.7.5, p. 32, supporting fact: each vector in the
    concatenation of two orthonormal families has norm one. *)
Lemma orthonormal_concatenation_unit i :
  inner_norm hB (concatenate_family e f i) = 1.
Proof.
apply: inner_norm_value; first exact: ler01.
rewrite expr1n /concatenate_family; case: (split i) => j;
  by rewrite (he, hf) eqxx.
Qed.

(** Source for [orthonormal_concatenation]: Federer 1.7.5,
    p. 32, cross-orthogonality is exactly what is needed to
    make the combined orthonormal families orthonormal. *)
Theorem orthonormal_concatenation :
  (forall i j, B (e i) (f j) = 0) -> orthonormal_family B (concatenate_family e f).
Proof.
move=> ho i j.
rewrite -(splitK i) -(splitK j).
case: (split i) => a; case: (split j) => b;
  rewrite /unsplit /= ?concatenate_family_l ?concatenate_family_r ?eq_shift.
- exact: he.
- exact: ho.
- by rewrite (inner_symmetric hB) ho.
- exact: hf.
Qed.
End Concatenation.
