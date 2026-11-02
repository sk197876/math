(** Federer (1969), 2.10.3, p. 172: the endpoint exterior-product map is
    affine separately in each variable. This supporting file first proves
    linearity of an indexed exterior product in each vector factor, using
    only the public exterior-word context laws from 1.4.1, p. 17. Source
    editions: ExteriorDiameterUP.v *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import ExteriorAlgebra ExteriorGrading FiniteExteriorPowers
  GradedComponents AlternatingExtension SeparateAffineHullBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_word_coordinate_linear]: supporting
    linear dependence on one unrepeated vector factor
    for the separate-affinity argument in Federer 2.10.3,
    p. 172. The coordinate list is arbitrary and need
    not enumerate the entire finite index type. *)
Lemma exterior_word_coordinate_linear (K : fieldType) (I : eqType) (V : lmodType K)
    (u : I -> V) (i : I) (s : seq I) : uniq s -> i \in s ->
  linear (fun x : V => exterior_word [seq coordinate_replacement u i x j | j <- s]).
Proof.
move=> hs hi; case/splitPr: hi hs=> p q hs.
have his : i \notin p.
  move: hs; rewrite cat_uniq /= negb_or=> /and3P[_ /andP[h _] _]; exact h.
have hiq : i \notin q.
  move: hs; rewrite cat_uniq /= => /and3P[_ _ /andP[h _]]; exact h.
have hmap (l : seq I) : i \notin l -> forall x,
    [seq coordinate_replacement u i x j | j <- l]=[seq u j | j <- l].
  move=> hi x; apply/eq_in_map=> j hj; rewrite /coordinate_replacement.
  have hji : j!=i by apply/eqP=> he; move: hi; rewrite -he hj.
  by rewrite (negPf hji).
have he x : [seq coordinate_replacement u i x j | j <- p++i::q]=
    [seq u j | j <- p]++x::[seq u j | j <- q].
  by rewrite map_cat /= /coordinate_replacement eqxx (hmap p his) (hmap q hiq).
move=> a x y; rewrite !he; exact: exterior_word_context_linear.
Qed.

(** Source for [exterior_coordinate_map]: supporting linear
    one-factor map for Federer 2.10.3, p. 172. This
    bundles the already proved factor-linearity law for
    use in the separate-affinity argument. *)
Definition exterior_coordinate_map (K : fieldType) (V : lmodType K)
    (m : nat) (u : 'I_m -> V) (i : 'I_m) (x : V) :=
  e_lambda (coordinate_replacement u i x) (ord_tuple m).

(** Source for [indexed_exterior_product_coordinate_linear]:
    supporting linear dependence of the degree-m product
    on an individual factor, for Federer 2.10.3,
    p. 172. Lift the public word law to the actual
    homogeneous component through its linear inclusion. *)
Theorem indexed_exterior_product_coordinate_linear (K : fieldType) (V : lmodType K)
    (m : nat) (u : 'I_m -> V) (i : 'I_m) :
  linear (fun x : V => e_lambda (coordinate_replacement u i x) (ord_tuple m)).
Proof.
move=> a x y; apply: val_inj.
change (component_val (e_lambda (coordinate_replacement u i (a *: x+y)) (ord_tuple m))=
  component_val (a *: e_lambda (coordinate_replacement u i x) (ord_tuple m)+
    e_lambda (coordinate_replacement u i y) (ord_tuple m))).
rewrite linearP !e_lambdaE.
exact (@exterior_word_coordinate_linear K (Choice.clone 'I_m _) V u i (ord_tuple m)
  (enum_uniq _) ltac:(by rewrite /ord_tuple /= mem_enum) a x y).
Qed.
HB.instance Definition _ (K : fieldType) (V : lmodType K)
    (m : nat) (u : 'I_m -> V) (i : 'I_m) :=
  GRing.isLinear.Build K V (exterior_power V m) *:%R (exterior_coordinate_map u i)
    (@indexed_exterior_product_coordinate_linear K V m u i).
