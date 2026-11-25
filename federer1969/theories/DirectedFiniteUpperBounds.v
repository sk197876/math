(** General set-theoretic support for the inverse-limit paragraph of Federer
    (1969), 2.6.6, pp. 120–121: every finite family of indices has a common
    upper index. Source context: CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot finmap classical_sets.
From Federer Require Import CompactInverseSystemUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [directed_list_upper_bound]: supporting finite
    induction on the directedness condition used in Federer 2.6.6,
    pp. 120–121. A prescribed starting index is also dominated. *)
Lemma directed_list_upper_bound (I : choiceType) (le : I -> I -> Prop)
    (hD : is_directed_preorder le) (i0 : I) (s : seq I) :
  exists k, le i0 k /\ forall i, i \in s -> le i k.
Proof.
elim: s=> [|i s [k [h0 hk]]].
- exists i0; split; first exact: (@directed_preorder_reflexive I le hD i0).
  by move=> i; rewrite in_nil.
- have [m [him hkm]] := directed_preorder_upper hD i k.
  exists m; split; first exact: (@directed_preorder_transitive I le hD i0 k m h0 hkm).
  move=> j; rewrite in_cons=> /orP[/eqP ->|hj]; first exact: him.
  exact: (@directed_preorder_transitive I le hD j k m (hk j hj) hkm).
Qed.

(** Source for [directed_finite_upper_bound]: a common upper
    index for finitely many coordinate constraints, supporting the
    compactness argument in Federer 2.6.6, pp. 120–121. *)
Lemma directed_finite_upper_bound (I : choiceType) (le : I -> I -> Prop)
    (hD : is_directed_preorder le) (i0 : I) (F : {fset I}) :
  exists k, le i0 k /\ forall i, i \in F -> le i k.
Proof. exact: directed_list_upper_bound hD i0 (enum_fset F). Qed.
