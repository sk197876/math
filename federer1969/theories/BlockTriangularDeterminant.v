(** Determinants of block triangular maps, supporting Federer (1969),
    2.7.16, example (3), printed pp. 137–138: "left multiplication by g in G
    maps phi x psi onto |det(g|W)|^{-m} phi x |det g|^{m-n} psi", and
    "det(wedge^1 g) = det(g) = det(g|W) det(wedge^1 g|W')". The determinant
    is det of 1.3.4, p. 16 (ExteriorDeterminant.v), defined through the
    action on the top exterior power. Suppose Y has a base consisting of the
    vectors iota_k(a_i), k < p1, i < q1, followed by the vectors
    kappa_j(c_l), j < p2, l < q2, where a, c are bases of U1, U2 and iota_k,
    kappa_j are linear maps into Y. If an endomorphism T of Y satisfies T o
    iota_k = iota_k o h and T(kappa_j(v)) - kappa_j(h'(v)) lies in the span
    of the first group of base vectors, then det T = (det h)^{p1} (det
    h')^{p2} (triangular_block_det). The product of the base vectors is the
    product of the first group followed by the product of the second; T
    multiplies each block of the first group by det h, and in the second
    group the summands in the span of the first group do not contribute,
    because a product containing a vector twice vanishes
    (exterior_word_span_shift). With p2 = 0 or p1 = 0 this is
    block_det_power of BlockDeterminant.v. No matrices are used. neither
    treats block triangular maps. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import LinearBasis FiniteIndependence TensorUP ExteriorBases ExteriorAlgebra
  ExteriorGrading ExteriorMaps ExteriorDeterminant ExteriorLeibniz ExteriorExpansion AlternatingExtension
  BlockDeterminant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section SpanShift.
Variable K : fieldType.
Variable Y : lmodType K.

(** Source for [context_word_fun]: the multilinearity of the exterior
    product in one factor, Federer 1.3.1, p. 13, used for
    "det(wedge^1 g) = det(g|W) det(wedge^1 g|W')", 2.7.16, p. 138.
    Definition of v |-> s_1 wedge ... wedge v wedge t_1 wedge .... *)
Definition context_word_fun (s t : seq Y) (v : Y) : exterior_space Y := exterior_word (s ++ v :: t).

HB.instance Definition _ (s t : seq Y) := GRing.isLinear.Build K Y (exterior_space Y) *:%R
  (context_word_fun s t) (exterior_word_context_linear s t).

(** Source for [context_word]: the linear map
    v |-> s_1 wedge ... wedge v wedge t_1 wedge ..., Federer 1.3.1,
    p. 13; supporting 2.7.16, p. 138. Definition. *)
Definition context_word (s t : seq Y) : {linear Y -> exterior_space Y} :=
  GRing.Linear.clone _ _ _ _ (context_word_fun s t) _.

(** Source for [exterior_word_span_zero]: a product of vectors vanishes
    if one factor is a linear combination of factors preceding it,
    Federer 1.3.1, p. 13 (the exterior product is alternating);
    supporting "det(wedge^1 g) = det(g|W) det(wedge^1 g|W')", 2.7.16,
    p. 138. Supporting lemma. *)
Lemma exterior_word_span_zero (I : eqType) (F : I -> Y) (r : seq I) (M t : seq Y) (d : I -> K) :
  exterior_word ([seq F i | i <- r] ++ M ++ (\sum_(i <- r) d i *: F i) :: t) = 0.
Proof.
rewrite catA.
change (context_word ([seq F i | i <- r] ++ M) t (\sum_(i <- r) d i *: F i) = 0).
rewrite linear_sum; apply: big1_seq=> i /andP [_ hi]; rewrite linearZ /=.
rewrite /context_word_fun exterior_word_nonuniq ?scaler0 //.
rewrite cat_uniq negb_and negb_and; apply/orP; right; apply/orP; left.
rewrite negbK /=; apply/orP; left.
by rewrite mem_cat (map_f F hi).
Qed.

(** Source for [exterior_word_span_shift]: adding to the factors y_j
    linear combinations of a prefix s_1, ..., s_p does not change the
    product s_1 wedge ... wedge s_p wedge ... wedge y_j wedge ...,
    Federer 1.3.1, p. 13; supporting "det(wedge^1 g) =
    det(g|W) det(wedge^1 g|W')", 2.7.16, p. 138. Supporting lemma. *)
Lemma exterior_word_span_shift (I : eqType) (J : Type) (F : I -> Y) (r : seq I) (y z : J -> Y) (s : seq J)
    (M : seq Y) :
  (forall j, exists d : I -> K, z j = \sum_(i <- r) d i *: F i) ->
  exterior_word ([seq F i | i <- r] ++ M ++ [seq y j + z j | j <- s]) =
    exterior_word ([seq F i | i <- r] ++ M ++ [seq y j | j <- s]).
Proof.
move=> hz; elim: s M=> [|j s ih] M //=.
have [d hd] := hz j.
rewrite !catA.
transitivity (context_word ([seq F i | i <- r] ++ M) [seq y j0 + z j0 | j0 <- s] (y j + z j));
  first by [].
rewrite linearD /= /context_word_fun hd -!catA exterior_word_span_zero addr0.
by rewrite -!cat_rcons ih.
Qed.

End SpanShift.

Section Enumeration.

(** Source for [sum_enumE]: the base of Y in Federer 2.7.16, p. 137,
    lists the first group of base vectors before the second: the
    enumeration of a sum type lists the left summand first. Supporting
    lemma. *)
Lemma sum_enumE (T1 T2 : finType) :
  enum {: T1 + T2} = [seq inl x | x <- enum T1] ++ [seq inr y | y <- enum T2].
Proof. by rewrite !enumT [in LHS]unlock. Qed.

End Enumeration.

Section TriangularBlocks.
Variable K : fieldType.
Hypothesis h2 : (1 + 1 : K) != 0.
Variables U1 U2 Y : lmodType K.
Variables p1 q1 p2 q2 : nat.
Variable a : 'I_q1 -> U1.
Hypothesis ha : is_basis a.
Variable c : 'I_q2 -> U2.
Hypothesis hc : is_basis c.
Variable iota : 'I_p1 -> {linear U1 -> Y}.
Variable kappa : 'I_p2 -> {linear U2 -> Y}.
Local Notation I1 := ('I_p1 * 'I_q1)%type.
Local Notation I2 := ('I_p2 * 'I_q2)%type.
Local Notation I := (I1 + I2)%type.

(** Source for [linear_word_scale]: f(g(a_1)) wedge ... wedge f(g(a_q))
    = det g . f(a_1) wedge ... wedge f(a_q) for linear maps f, g, by
    1.3.4, p. 16, and the functoriality of the exterior algebra (1.4.1,
    p. 18); supporting 2.7.16, pp. 137–138. Supporting lemma. *)
Lemma linear_word_scale (U : lmodType K) q (e : 'I_q -> U) (he : is_basis e)
    (f : {linear U -> Y}) (g : {linear U -> U}) :
  exterior_word [seq f (g (e i)) | i <- enum 'I_q] =
    det h2 he g *: exterior_word [seq f (e i) | i <- enum 'I_q].
Proof.
have h1 : exterior_word [seq f (g (e i)) | i <- enum 'I_q] =
    exterior_algebra_map f (exterior_word [seq g (e i) | i <- enum 'I_q]).
  rewrite exterior_algebra_map_word.
  exact: (congr1 exterior_word (map_comp f (fun i => g (e i)) (enum 'I_q))).
have h3 : exterior_word [seq f (e i) | i <- enum 'I_q] =
    exterior_algebra_map f (exterior_word [seq e i | i <- enum 'I_q]).
  rewrite exterior_algebra_map_word.
  exact: (congr1 exterior_word (map_comp f e (enum 'I_q))).
have h4 : exterior_word [seq g (e i) | i <- enum 'I_q] =
    component_val (exterior_power_map g q (top_vector e)).
  by rewrite top_map_word.
rewrite h1 h3 h4 (detE h2 he g (top_vector e)).
change (exterior_algebra_map f (det h2 he g *: exterior_word [seq e i | i <- enum 'I_q]) =
  det h2 he g *: exterior_algebra_map f (exterior_word [seq e i | i <- enum 'I_q])).
exact: linearZ.
Qed.

(** Source for [blocks_word]: the product of the vectors iota_k(w_i),
    enumerated with k major, is the product over k of the block
    products, Federer 1.3.1, p. 13; supporting 2.7.16, p. 137.
    Supporting lemma. *)
Lemma blocks_word (p q : nat) (U : lmodType K) (w : 'I_q -> U) (F : 'I_p -> U -> Y) :
  exterior_word [seq F x.1 (w x.2) | x <- enum {: 'I_p * 'I_q}] =
    foldr (@wedge K Y) (exterior_unit Y)
      [seq exterior_word [seq F k (w i) | i <- enum 'I_q] | k <- enum 'I_p].
Proof.
rewrite (pair_enum_flatten (fun k i => F k (w i))).
elim: (enum 'I_p)=> [|k s ih] //=.
by rewrite -exterior_word_cat ih.
Qed.

(** Source for [blocks_word_scale]: if each block product is multiplied
    by d, the product of all p blocks is multiplied by d^p, Federer
    1.3.1, p. 13; supporting 2.7.16, p. 137. Supporting lemma. *)
Lemma blocks_word_scale (p q : nat) (U : lmodType K) (w : 'I_q -> U) (F G : 'I_p -> U -> Y) (d : K) :
  (forall k, exterior_word [seq G k (w i) | i <- enum 'I_q] =
    d *: exterior_word [seq F k (w i) | i <- enum 'I_q]) ->
  exterior_word [seq G x.1 (w x.2) | x <- enum {: 'I_p * 'I_q}] =
    d ^+ p *: exterior_word [seq F x.1 (w x.2) | x <- enum {: 'I_p * 'I_q}].
Proof.
move=> hd; rewrite (blocks_word w G) (blocks_word w F).
under eq_map do rewrite hd.
by rewrite (wedge_foldr_scale d) -cardE card_ord.
Qed.

(** Source for [triangular_pairs]: the base vectors iota_k(a_i) and
    kappa_j(c_l), indexed by the disjoint union of the two sets of
    pairs, supporting the decomposition X ~ Hom(W, W) x Hom(Z, V) of
    Federer 2.7.16, p. 137. Definition. *)
Definition triangular_pairs (x : I) : Y :=
  match x with inl x1 => iota x1.1 (a x1.2) | inr x2 => kappa x2.1 (c x2.2) end.

(** Source for [triangular_family]: the family triangular_pairs indexed
    by the ordinals below the number of pairs through enum_val,
    supporting Federer 2.7.16, p. 137. Definition. *)
Definition triangular_family (j : 'I_#|{: I}|) : Y := triangular_pairs (enum_val j).

Hypothesis hF : is_basis triangular_family.
Variables (T : {linear Y -> Y}) (h : {linear U1 -> U1}) (h' : {linear U2 -> U2}).
Hypothesis hT1 : forall k u, T (iota k u) = iota k (h u).
Hypothesis hT2 : forall j v, exists d : I1 -> K,
  T (kappa j v) = kappa j (h' v) + \sum_x d x *: iota x.1 (a x.2).

(** Source for [triangular_family_word]: the product of the base
    vectors of Y, transformed by F, is the product of the first group
    followed by the product of the second group, Federer 1.3.1, p. 13;
    supporting 2.7.16, pp. 137–138. Supporting lemma. *)
Lemma triangular_family_word (G : Y -> Y) :
  exterior_word [seq G (triangular_family j) | j <- enum 'I_#|{: I}|] =
    wedge (exterior_word [seq G (iota x.1 (a x.2)) | x <- enum {: I1}])
      (exterior_word [seq G (kappa y.1 (c y.2)) | y <- enum {: I2}]).
Proof.
rewrite (enum_val_map (fun x : I => G (triangular_pairs x))) sum_enumE map_cat.
by rewrite -!map_comp exterior_word_cat.
Qed.

(** Source for [triangular_block_det]: "det T = (det h)^{p1}
    (det h')^{p2}" for a block triangular endomorphism T of Y, the
    determinant computation behind "left multiplication by g in G maps
    phi x psi onto |det(g|W)|^{-m} phi x |det g|^{m-n} psi" and
    "det(wedge^1 g) = det(g|W) det(wedge^1 g|W')", Federer 2.7.16,
    pp. 137–138, with det of 1.3.4, p. 16. Supporting theorem. *)
Theorem triangular_block_det : det h2 hF T = det h2 ha h ^+ p1 * det h2 hc h' ^+ p2.
Proof.
apply: (@top_scalar_injective K h2 _ Y triangular_family hF).
rewrite -detE; apply: val_inj.
change (exterior_algebra_map T (exterior_word [seq triangular_family j | j <- enum 'I_#|{: I}|]) =
  (det h2 ha h ^+ p1 * det h2 hc h' ^+ p2) *:
    exterior_word [seq triangular_family j | j <- enum 'I_#|{: I}|]).
rewrite exterior_algebra_map_word -map_comp.
have -> : [seq (T \o triangular_family) j | j <- enum 'I_#|{: I}|] =
    [seq T (triangular_family j) | j <- enum 'I_#|{: I}|] by [].
rewrite (triangular_family_word T) (triangular_family_word id).
have h1 : exterior_word [seq T (iota x.1 (a x.2)) | x <- enum {: I1}] =
    det h2 ha h ^+ p1 *: exterior_word [seq iota x.1 (a x.2) | x <- enum {: I1}].
  apply: (blocks_word_scale (F := fun k u => iota k u) (G := fun k u => T (iota k u))).
  move=> k.
  have -> : [seq T (iota k (a i)) | i <- enum 'I_q1] = [seq iota k (h (a i)) | i <- enum 'I_q1].
    by apply: eq_map=> i; exact: hT1.
  exact: linear_word_scale.
pose z (y : I2) := T (kappa y.1 (c y.2)) - kappa y.1 (h' (c y.2)).
have hz y : exists d : I1 -> K, z y = \sum_(x <- enum {: I1}) d x *: iota x.1 (a x.2).
  have [d hd] := hT2 y.1 (c y.2).
  by exists d; rewrite big_enum /z hd addrC addKr.
have h3 : [seq T (kappa y.1 (c y.2)) | y <- enum {: I2}] =
    [seq kappa y.1 (h' (c y.2)) + z y | y <- enum {: I2}].
  by apply: eq_map=> y; rewrite /z addrC subrK.
have h4 : exterior_word [seq kappa y.1 (h' (c y.2)) | y <- enum {: I2}] =
    det h2 hc h' ^+ p2 *: exterior_word [seq kappa y.1 (c y.2) | y <- enum {: I2}].
  apply: (blocks_word_scale (F := fun j v => kappa j v) (G := fun j v => kappa j (h' v))).
  by move=> j; exact: linear_word_scale.
rewrite h1 (bilZl (wedge_bilinear Y)) h3 exterior_word_cat.
have h5 := @exterior_word_span_shift K Y I1 I2 (fun x => iota x.1 (a x.2)) (enum {: I1})
  (fun y => kappa y.1 (h' (c y.2))) z (enum {: I2}) [::] hz.
rewrite /= in h5; rewrite h5 -exterior_word_cat h4 (bilZr (wedge_bilinear Y)) scalerA.
by [].
Qed.

End TriangularBlocks.
