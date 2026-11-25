(** Federer (1969), 1.10.5, p. 48: supporting bounded extension from a
    finite-dimensional subspace, using the locally proved finite-valued
    Hahn-Banach theorem (2.4.12, p. 86). This lemma isolates the
    coordinate-extension step of those proofs. It applies to any injective
    linear inclusion, with no dimension restriction on either space. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP RealSeminormOperations PartialLinearMap
  HahnBanach SeminormNormingFunctional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [bounded_functional_extension]: Federer 1.10.5, p. 48,
    supporting extension argument from 2.4.12, p. 86. A functional bounded
    by C times the ambient norm on a linear subspace extends with the same
    bound. *)
Theorem bounded_functional_extension (R : realType) (U V : lmodType R)
    (N : V -> R) (hN : is_real_seminorm N)
    (j : {linear U -> V}) (hj : injective j)
    (f : {linear U -> R^o}) C (hC : 0 <= C)
    (hb : forall u, `|f u| <= C * N (j u)) :
  exists g : {linear V -> R^o},
    (forall u, g (j u) = f u) /\ forall v, `|g v| <= C * N v.
Proof.
pose G := fun v a => exists u, v=j u /\ a=f u.
have hG : linear_graph G.
  split; first by exists 0; rewrite !linear0.
  split.
  - move=> x y a b [u [-> ->]] [v [-> ->]].
    exists (u+v); by rewrite !linearD.
  split.
  - move=> c x a [u [-> ->]]; exists (c*:u); by rewrite !linearZ.
  - move=> x a b [u [hxu ->]] [v [hxv ->]].
    have huv : u=v by apply: hj; rewrite -hxu -hxv.
    by rewrite huv.
have hCN := real_seminorm_positive_multiple hN hC.
have hd : forall v a, G v a -> a <= C * N v.
  move=> v a [u [-> ->]]; exact: le_trans (ler_norm (f u)) (hb u).
have [g [hg hgb]] := seminorm_hahn_banach hCN hG hd.
exists g; split.
- move=> u; apply: hg; by exists u.
- exact (@dominated_functional_absolute_bound R V (fun x => C * N x) hCN g hgb).
Qed.
