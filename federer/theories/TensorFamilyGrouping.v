(** Federer 1.1.2, p. 10: grouping the first m and last k factors gives
    mutually inverse linear maps. The proof successively applies the two
    abstract block universal properties and never unfolds a tensor space. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import TensorUP TensorFamily TensorFamilyLift TensorFamilyBlocks
  TensorProduct TensorSpan Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Grouping.
Variable K : fieldType.
Variables m k : nat.
Variable V : 'I_(m+k) -> lmodType K.
Local Notation A := {dffun forall i : 'I_m, V (lshift k i)}.
Local Notation B := {dffun forall i : 'I_k, V (rshift m i)}.
Local Notation C := {dffun forall i, V i}.
Variables L R : lmodType K.
Variables (muL : A -> L) (muR : B -> R).
Hypotheses (hL : is_tensor_product_family muL) (hR : is_tensor_product_family muR).

(** Source for [tensor_grouped_pure]: Federer 1.1.2, p. 10, second
    displayed isomorphism; the pure product in the two grouped blocks. *)
Definition tensor_grouped_pure (x : C) : tensor_space L R :=
  tensor_inj (muL (tensor_block_left x)) (muR (tensor_block_right x)).

(** Source for [tensor_grouped_multilinear]: Federer 1.1.2, p. 10;
    grouping the arguments preserves multilinearity in each original slot. *)
Lemma tensor_grouped_multilinear : multilinear tensor_grouped_pure.
Proof.
move=> x i; case: (split_ordP i)=> j ->; move=> a v w;
  rewrite /tensor_grouped_pure.
- rewrite !tensor_block_left_with_left !tensor_block_right_with_left
    (tensor_family_multilinear hL) tensor_inj_addl tensor_inj_scalel.
  reflexivity.
- rewrite !tensor_block_left_with_right !tensor_block_right_with_right
    (tensor_family_multilinear hR) tensor_inj_addr tensor_inj_scaler.
  reflexivity.
Qed.

(** Source for [tensor_grouped_ext]: Federer 1.1.2, p. 10;
    equality on pure tuples of both blocks determines a linear map.
    Supporting uniqueness argument from the two block spanning laws. *)
Lemma tensor_grouped_ext (Z : lmodType K)
    (f g : {linear tensor_space L R -> Z}) :
  (forall a b, f (tensor_inj (muL a) (muR b)) =
               g (tensor_inj (muL a) (muR b))) -> forall t, f t = g t.
Proof.
move=> he; apply: (tensor_ext (tensor_exists L R) f g)=> l r.
elim/(tensor_family_induction hL): l=> [|l l' hl hl'|c l hl|a].
- by rewrite tensor_inj0l !linear0.
- by rewrite tensor_inj_addl !linearD hl hl'.
- by rewrite tensor_inj_scalel !linearZ hl.
elim/(tensor_family_induction hR): r=> [|r r' hr hr'|c r hr|b].
- by rewrite tensor_inj0r !linear0.
- by rewrite tensor_inj_addr !linearD hr hr'.
- by rewrite tensor_inj_scaler !linearZ hr.
- exact: he.
Qed.

Section Factorisation.
Variable Z : lmodType K.
Variable beta : C -> Z.
Hypothesis hb : multilinear beta.

(** Source for [tensor_group_beta_left_multilinear]: Federer 1.1.2,
    p. 10; fix the second block and vary the first block's arguments. *)
Lemma tensor_group_beta_left_multilinear b :
  multilinear (fun a => beta (tensor_block_join a b)).
Proof. by move=> a i c v w; rewrite !tensor_block_join_with_left; exact: hb. Qed.

(** Source for [tensor_group_beta_left]: Federer 1.1.2, p. 10;
    the first block's unique universal factorisation. *)
Definition tensor_group_beta_left b : {linear L -> Z} :=
  abstract_tensor_family_lift hL (tensor_group_beta_left_multilinear b).

(** Source for [tensor_group_beta_right_multilinear]: Federer 1.1.2,
    p. 10; the first universal extension stays multilinear in the second
    block, by spanning of the first block's pure products. *)
Lemma tensor_group_beta_right_multilinear l :
  multilinear (fun b => tensor_group_beta_left b l).
Proof.
elim/(tensor_family_induction hL): l=> [|l l' hl hl'|a l hl|u];
  move=> x i c v w; rewrite /tensor_group_beta_left.
- by rewrite !linear0 ?scaler0 ?addr0 ?add0r.
- rewrite !linearD /=; fold tensor_group_beta_left.
  by rewrite hl hl' ?scalerDr addrACA.
- rewrite !linearZ /=; fold tensor_group_beta_left.
  by rewrite hl ?scalerDr !scalerA (mulrC a c).
- rewrite !abstract_tensor_family_liftE !tensor_block_join_with_right.
  exact: hb.
Qed.

(** Source for [tensor_group_beta_double]: Federer 1.1.2, p. 10;
    the second block's unique universal factorisation. *)
Definition tensor_group_beta_double l : {linear R -> Z} :=
  abstract_tensor_family_lift hR (tensor_group_beta_right_multilinear l).

(** Source for [tensor_group_beta_doubleE]: Federer 1.1.2, p. 10;
    both block extensions retain the original multilinear value. *)
Lemma tensor_group_beta_doubleE a b :
  tensor_group_beta_double (muL a) (muR b) = beta (tensor_block_join a b).
Proof.
by rewrite /tensor_group_beta_double abstract_tensor_family_liftE
  /tensor_group_beta_left abstract_tensor_family_liftE.
Qed.

(** Source for [tensor_group_beta_bilinear]: Federer 1.1.2, p. 10;
    two successive universal extensions give a bilinear function on the
    two tensor spaces, permitting their ordinary tensor universal property. *)
Lemma tensor_group_beta_bilinear : bilinear tensor_group_beta_double.
Proof.
split; last by move=> l; exact: linearP.
move=> r c l l'; elim/(tensor_family_induction hR): r=> [|r r' hr hr'|a r hr|b].
- by rewrite !linear0 ?scaler0 ?addr0 ?add0r.
- by rewrite !linearD /= hr hr' ?scalerDr addrACA.
- by rewrite !linearZ /= hr ?scalerDr !scalerA (mulrC a c).
- by rewrite /tensor_group_beta_double !abstract_tensor_family_liftE
    /tensor_group_beta_left linearP.
Qed.

(** Source for [tensor_group_factorisation_exists]: Federer 1.1.2,
    p. 10; every original multilinear map factors through grouped products. *)
Lemma tensor_group_factorisation_exists :
  exists f : {linear tensor_space L R -> Z},
    forall x, f (tensor_grouped_pure x) = beta x.
Proof.
exists (GRing.Linear.clone _ _ _ _ (tensor_lift tensor_group_beta_bilinear) _)=> x.
change (tensor_lift tensor_group_beta_bilinear (tensor_grouped_pure x) = beta x).
by rewrite /tensor_grouped_pure tensor_liftE tensor_group_beta_doubleE tensor_block_joinK.
Qed.
End Factorisation.

(** Source for [tensor_grouped_universal_property]: Federer 1.1.2,
    p. 10; the grouped tensor space satisfies the original full-family
    universal property. No grouping or factorisation law is assumed. *)
Theorem tensor_grouped_universal_property : is_tensor_product_family tensor_grouped_pure.
Proof.
constructor; first exact: tensor_grouped_multilinear.
move=> Z beta hb; have [f hf] := tensor_group_factorisation_exists hb.
exists f; split=> //; move=> g hg; apply: tensor_grouped_ext=> a b.
have hf' := hf (tensor_block_join a b); have hg' := hg (tensor_block_join a b).
by rewrite /tensor_grouped_pure tensor_block_join_left tensor_block_join_right in hf' hg'; rewrite hg' hf'.
Qed.

(** Source for [tensor_family_grouping_isomorphism]: Federer 1.1.2,
    p. 10, second displayed isomorphism. Grouping any two consecutive
    blocks gives mutually inverse linear maps with the printed pure law.
    Zero-size blocks are also allowed as a supporting extension. *)
Theorem tensor_family_grouping_isomorphism
    (T : lmodType K) (mu : C -> T) (hmu : is_tensor_product_family mu) :
  exists (F : {linear tensor_space L R -> T})
         (G : {linear T -> tensor_space L R}),
    (forall a b, F (tensor_inj (muL a) (muR b)) = mu (tensor_block_join a b)) /\
    (forall x, G (mu x) = tensor_grouped_pure x) /\ cancel F G /\ cancel G F.
Proof.
have [F [G [hF [hG [hFG [hGF _]]]]]] :=
  tensor_family_unique tensor_grouped_universal_property hmu.
exists F, G; split; last by split=> //; split.
move=> a b; have h := hF (tensor_block_join a b).
by rewrite /tensor_grouped_pure tensor_block_join_left tensor_block_join_right in h.
Qed.
End Grouping.
