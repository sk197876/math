(** Federer (1969), 1.8.2, p. 40: a full paired basis of
    a 2m-dimensional space has exactly m pairs. This supports the
    use of the normal form on complex associated subspaces and the
    sharp-comass construction. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import LinearBasis FiniteBasisComparison SkewNormalFormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [paired_basis_count]: Federer 1.8.2,
    p. 40, the pair count is half the real dimension, including zero. *)
Theorem paired_basis_count (R : fieldType) (V : lmodType R)
    m (e : 'I_(m+m) -> V) (he : is_basis e)
    k (a b : 'I_k -> V) (hp : is_basis (paired_family a b)) : k = m.
Proof.
pose I := Finite.clone ('I_k * bool)%type _.
have hb := @basis_reindex R (Choice.clone I _) (Choice.clone 'I_(#|I|) _) V
  (paired_family a b) hp enum_rank enum_val (@enum_rankK I) (@enum_valK I).
have hs := finite_basis_size he hb.
rewrite /I card_prod card_ord card_bool muln2 addnn in hs.
exact: esym (double_inj hs).
Qed.
