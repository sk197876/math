(** Supporting Hahn–Banach extension for the closed-subspace reflexivity
    assertion in Federer (1969), 2.9.22, p. 167. The extension follows from
    the book's theorem 2.4.12, p. 86, applied to the graph of the functional
    on the actual subspace. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ModuleQuotient SubspaceCarrier LinearRetraction PartialLinearMap
  RealNormUP RealSeminormOperations NormedSubspace HahnBanach SeminormNormingFunctional
  ContinuousRealFunctional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [bounded_subspace_functional_extension]: supporting
    norm-controlled extension needed in Federer 2.9.22, p. 167,
    to represent every continuous subspace functional by a
    restriction of an ambient one. Hahn–Banach, 2.4.12,
    p. 86, extends its linear graph while retaining the
    given nonnegative bound C. No extension axiom is added. *)
Theorem bounded_subspace_functional_extension (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (Z : subspace E)
    (f : {linear subspace_space Z -> R^o}) (C : R) :
  0<=C -> (forall z, `|f z|<=C * subspace_norm N Z z) ->
  exists a : {linear E -> R^o},
    (forall z, a (subspace_val z)=f z) /\
    (forall y, `|a y|<=C * N y) /\ is_continuous_real_functional hN a.
Proof.
move=> hC hf.
pose i := @subspace_inclusion R E Z.
pose G := @image_graph R [the lmodType R of subspace_space Z] E R^o i f.
have hG : linear_graph G.
  exact (@image_graph_linear R [the lmodType R of subspace_space Z] E R^o i
    (@subspace_val_injective R E Z) f).
have hdom x b : G x b -> b<=C * N x.
  move=> [z [hz hb]].
  rewrite -hb -hz; exact: le_trans (ler_norm (f z)) (hf z).
have hCN := real_seminorm_positive_multiple hN.1 hC.
have [a [ha hb]] := seminorm_hahn_banach hCN hG hdom.
have hbound := dominated_functional_absolute_bound hCN hb.
exists a; split.
  move=> z; apply: (ha (subspace_val z) (f z)); by exists z.
split=> //; exact (@bounded_real_functional_continuous R E N hN a C hC hbound).
Qed.
