(** Determinants of block maps, supporting Federer (1969), 2.7.16, example
    (2), printed pp. 136–137: "using a base e_1, ..., e_m of U we construct
    a G action preserving isomorphism X ~ V^m by mapping f in X onto
    (f(e_1), ..., f(e_m))", and "|det(wedge^1 g)^{-1}|^{-n} = |det g|^n".
    The determinant is that of 1.3.4, p. 16 (det of ExteriorDeterminant.v),
    defined through the action on the top exterior power. Suppose X has a
    base indexed by the pairs (k, i), k < p, i < q, whose (k, i) member is
    iota_k(w_i), where w_1, ..., w_q is a base of W and iota_1, ..., iota_p
    are linear maps of W into X. If T is an endomorphism of X with T o
    iota_k = iota_k o h for every k, then det T = (det h)^p
    (block_det_power): the product of the base vectors of X is the product
    over k of the products iota_k(w_1) wedge ... wedge iota_k(w_q), and T
    multiplies each factor by det h. The pairs are enumerated through
    enum_val, in the order (k, i) with k major. The module also proves
    det(wedge^1 h) = det h for the dual map wedge^1 h: omega |-> omega o h
    of wedge^1 W = Hom(W, R), by the permutation formula of 1.3.4 and the
    equality of the indices of a permutation and of its inverse
    (dual_map_det). No matrices are used: the coefficients are the values of
    the dual base on h(w_i). *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import fingroup perm.
From Federer Require Import LinearBasis FiniteIndependence FiniteBasisCriterion FiniteDualDimension
  Annihilator Hom TensorUP ExteriorBases ExteriorAlgebra ExteriorGrading ExteriorMaps
  ExteriorDeterminant ExteriorLeibniz InversionCount PermutationDeterminant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Enumeration.
Variable T : finType.

(** Source for [enum_val_map]: the enumeration of the pairs (k, i) used
    for the base of X ~ V^m in Federer 2.7.16, p. 136: listing the
    ordinals below #|T| through enum_val lists T in its enumeration
    order. Supporting lemma. *)
Lemma enum_val_map (Y : Type) (F : T -> Y) :
  map (fun j : 'I_#|{: T}| => F (enum_val j)) (enum 'I_#|{: T}|) = map F (enum T).
Proof.
case: (posnP #|{: T}|)=> hT.
  have h0 : enum T = [::] by apply: size0nil; rewrite -cardE hT.
  rewrite h0; apply: size0nil; rewrite size_map size_enum_ord; exact: hT.
pose x0 : T := enum_val (Ordinal hT).
have hs : size (enum 'I_#|{: T}|) = #|{: T}| := size_enum_ord _.
apply: (@eq_from_nth _ (F x0)).
  by rewrite (size_map F) (size_map (fun j : 'I_#|{: T}| => F (enum_val j))) hs cardE.
move=> i; rewrite (size_map (fun j : 'I_#|{: T}| => F (enum_val j))) hs=> hi.
rewrite (nth_map (Ordinal hi)) ?hs // (nth_map x0); last by rewrite -cardE.
have -> : nth (Ordinal hi) (enum 'I_#|{: T}|) i = Ordinal hi.
  by apply: val_inj; rewrite /= nth_enum_ord.
by rewrite (enum_val_nth x0).
Qed.

End Enumeration.

(** Source for [pair_enum_flatten]: the order (k, i) with k major of the
    pairs indexing the base of X ~ V^m, Federer 2.7.16, p. 136.
    Supporting lemma: the enumeration of 'I_p x 'I_q lists the blocks
    (k, 1), ..., (k, q) for k = 1, ..., p in turn. *)
Lemma pair_enum_flatten (p q : nat) (Y : Type) (F : 'I_p -> 'I_q -> Y) :
  [seq F x.1 x.2 | x <- enum {: 'I_p * 'I_q}] =
    flatten [seq [seq F k i | i <- enum 'I_q] | k <- enum 'I_p].
Proof.
rewrite enumT unlock /= /prod_enum.
elim: (enum 'I_p)=> [|k s ih] //=.
by rewrite map_cat ih -map_comp.
Qed.

Section Block.
Variable K : fieldType.
Hypothesis h2 : (1 + 1 : K) != 0.
Variables W X : lmodType K.
Variables p q : nat.
Variable w : 'I_q -> W.
Hypothesis hw : is_basis w.
Variable iota : 'I_p -> {linear W -> X}.
Local Notation I := ('I_p * 'I_q)%type.

(** Source for [block_family]: the base of X corresponding to the base
    e_k |-> v_i of V^m under the isomorphism X ~ V^m of Federer 2.7.16,
    p. 136: its (k, i) member is iota_k(w_i). Definition, indexed by the
    ordinals below #|'I_p x 'I_q| through enum_val. *)
Definition block_family (j : 'I_#|{: I}|) : X := iota (enum_val j).1 (w (enum_val j).2).

Hypothesis he : is_basis block_family.
Variables (T : {linear X -> X}) (h : {linear W -> W}).
Hypothesis hT : forall k v, T (iota k v) = iota k (h v).

(** Source for [block_family_word]: the product of the base vectors of X
    is the product over k of iota_k(w_1) wedge ... wedge iota_k(w_q),
    supporting Federer 2.7.16, p. 136, with 1.3.4, p. 16. Supporting
    lemma. *)
Lemma block_family_word (F : X -> X) :
  exterior_word [seq F (block_family j) | j <- enum 'I_#|{: I}|] =
    foldr (@wedge K X) (exterior_unit X)
      [seq exterior_word [seq F (iota k (w i)) | i <- enum 'I_q] | k <- enum 'I_p].
Proof.
rewrite (enum_val_map (fun x : I => F (iota x.1 (w x.2)))).
rewrite (pair_enum_flatten (fun k i => F (iota k (w i)))).
elim: (enum 'I_p)=> [|k s ih] //=.
by rewrite -exterior_word_cat ih.
Qed.

(** Source for [block_word_scale]: T multiplies the product
    iota_k(w_1) wedge ... wedge iota_k(w_q) by det h, because
    T o iota_k = iota_k o h and h acts on the top power of W by det h,
    Federer 1.3.4, p. 16; supporting 2.7.16, p. 136. *)
Lemma block_word_scale k :
  exterior_word [seq T (iota k (w i)) | i <- enum 'I_q] =
    det h2 hw h *: exterior_word [seq iota k (w i) | i <- enum 'I_q].
Proof.
have hm : [seq T (iota k (w i)) | i <- enum 'I_q] = [seq iota k (h (w i)) | i <- enum 'I_q].
  by apply: eq_map=> i; exact: hT.
rewrite hm.
have h1 : exterior_word [seq iota k (h (w i)) | i <- enum 'I_q] =
    exterior_algebra_map (iota k) (exterior_word [seq h (w i) | i <- enum 'I_q]).
  rewrite exterior_algebra_map_word.
  exact: (congr1 exterior_word (map_comp (iota k) (fun i => h (w i)) (enum 'I_q))).
have h3 : exterior_word [seq iota k (w i) | i <- enum 'I_q] =
    exterior_algebra_map (iota k) (exterior_word [seq w i | i <- enum 'I_q]).
  rewrite exterior_algebra_map_word.
  exact: (congr1 exterior_word (map_comp (iota k) w (enum 'I_q))).
have h4 : exterior_word [seq h (w i) | i <- enum 'I_q] =
    component_val (exterior_power_map h q (top_vector w)).
  by rewrite top_map_word.
rewrite h1 h3 h4 (detE h2 hw h (top_vector w)).
change (exterior_algebra_map (iota k) (det h2 hw h *: exterior_word [seq w i | i <- enum 'I_q]) =
  det h2 hw h *: exterior_algebra_map (iota k) (exterior_word [seq w i | i <- enum 'I_q])).
exact: linearZ.
Qed.

(** Source for [wedge_foldr_scale]: (a x_1) wedge ... wedge (a x_p) =
    a^p x_1 wedge ... wedge x_p, by the bilinearity of the exterior
    multiplication, Federer 1.3.1, p. 13; supporting 2.7.16, p. 136.
    Supporting lemma. *)
Lemma wedge_foldr_scale (J : Type) (a : K) (G : J -> exterior_space X) (s : seq J) :
  foldr (@wedge K X) (exterior_unit X) [seq a *: G x | x <- s] =
    a ^+ size s *: foldr (@wedge K X) (exterior_unit X) [seq G x | x <- s].
Proof.
elim: s=> [|x s ih] /=; first by rewrite expr0 scale1r.
rewrite ih (bilZl (wedge_bilinear X)) (bilZr (wedge_bilinear X)) scalerA.
by rewrite exprS.
Qed.

(** Source for [block_det_power]: "det T = (det h)^p" for an
    endomorphism T of X with T o iota_k = iota_k o h, the determinant of
    the action of G on X ~ V^m in Federer 2.7.16, p. 136, and of left
    multiplication by (wedge^1 g)^{-1} on p. 137, with det of 1.3.4,
    p. 16. Supporting theorem. *)
Theorem block_det_power : det h2 he T = det h2 hw h ^+ p.
Proof.
apply: (@top_scalar_injective K h2 _ X block_family he).
rewrite -detE; apply: val_inj.
change (exterior_algebra_map T (exterior_word [seq block_family j | j <- enum 'I_#|{: I}|]) =
  det h2 hw h ^+ p *: exterior_word [seq block_family j | j <- enum 'I_#|{: I}|]).
rewrite exterior_algebra_map_word -map_comp.
have -> : [seq (T \o block_family) j | j <- enum 'I_#|{: I}|] =
    [seq T (block_family j) | j <- enum 'I_#|{: I}|] by [].
rewrite (block_family_word T) (block_family_word id).
under eq_map do rewrite block_word_scale.
by rewrite (wedge_foldr_scale (det h2 hw h)) -cardE card_ord.
Qed.

End Block.

(** Source for [permutation_index_inverse]: the index of a permutation
    and of its inverse agree, since index is multiplicative and
    index(sigma)^2 = 1, Federer 1.3.3–1.3.4, pp. 15–16; supporting
    det(wedge^1 h) = det h in 2.7.16, p. 137. Supporting lemma. *)
Lemma permutation_index_inverse (K : fieldType) (h2 : (1 + 1 : K) != 0) n (s : 'S_n) :
  FedererPermutation.index K s^-1 = FedererPermutation.index K s.
Proof.
have hsq : FedererPermutation.index K s * FedererPermutation.index K s = 1.
  by rewrite /FedererPermutation.index -exprMn mulrNN mulr1 expr1n.
have hinv : FedererPermutation.index K s^-1 * FedererPermutation.index K s = 1.
  by rewrite -(index_multiplicative h2) mulVg (index_one h2).
by rewrite -[LHS]mulr1 -hsq mulrA hinv mul1r.
Qed.

Section DualMap.
Variable K : fieldType.
Hypothesis h2 : (1 + 1 : K) != 0.
Variable V : lmodType K.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.

(** Source for [dual_map_fun]: the map wedge^1 h of wedge^1 V =
    Hom(V, R) into itself, omega |-> omega o h, of Federer 2.7.16,
    p. 137 ("the linear isomorphism wedge^1: Hom(V, V) ~
    Hom(wedge^1 V, wedge^1 V)"), with wedge^1 of 1.4.1. Definition of
    the function. *)
Definition dual_map_fun (h : {linear V -> V}) (omega : Hom V K^o) : Hom V K^o :=
  hom_comp omega (hom_of_linear h).

(** Source for [dual_map_linear]: omega |-> omega o h is linear,
    Federer 1.4.1 and 2.7.16, p. 137. Supporting lemma. *)
Lemma dual_map_linear (h : {linear V -> V}) : linear (dual_map_fun h).
Proof. exact: hom_precompose_linear. Qed.
HB.instance Definition _ (h : {linear V -> V}) := GRing.isLinear.Build K (Hom V K^o) (Hom V K^o) *:%R
  (dual_map_fun h) (dual_map_linear h).

(** Source for [dual_map]: wedge^1 h, Federer 2.7.16, p. 137, as a
    linear endomorphism of wedge^1 V = Hom(V, R). Definition packaging
    the map with its linearity. *)
Definition dual_map (h : {linear V -> V}) : {linear Hom V K^o -> Hom V K^o} :=
  GRing.Linear.clone _ _ _ _ (dual_map_fun h) _.

(** Source for [dual_mapE]: (wedge^1 h)(omega) = omega o h, Federer
    2.7.16, p. 137. Supporting lemma. *)
Lemma dual_mapE (h : {linear V -> V}) (omega : Hom V K^o) x : dual_map h omega x = omega (h x).
Proof. by []. Qed.

(** Source for [dual_map_det]: det(wedge^1 h) = det h, used in
    "|det(wedge^1 g)^{-1}|^{-n} = |det g|^n", Federer 2.7.16, p. 137:
    with a_{i,j} = w_j(h(w_i)) for the dual base w_1*, ..., w_n*, the
    permutation formula of 1.3.4, p. 16, gives
    det(wedge^1 h) = sum_s index(s) prod_i a_{s(i),i}, which is the sum
    for det h after the substitutions i = s^{-1}(j) and s |-> s^{-1}.
    Supporting theorem. *)
Theorem dual_map_det (h : {linear V -> V}) : det h2 (dual_basisP hb) (dual_map h) = det h2 hb h.
Proof.
pose a i j := (dual_basis hb j (h (b i)) : K).
have hd : forall i, dual_map h (dual_basis hb i) = \sum_(j < n) a j i *: dual_basis hb j.
  move=> i; rewrite [LHS](dual_basis_expansion hb); apply: eq_bigr=> j _.
  by rewrite dual_mapE.
have hh : forall i, h (b i) = \sum_(j < n) a i j *: b j.
  by move=> i; rewrite [LHS](basis_vector_expansion hb).
rewrite (det_formula h2 (dual_basisP hb) hd) (det_formula h2 hb hh).
rewrite (reindex_inj invg_inj) /=; apply: eq_bigr=> s _.
rewrite (permutation_index_inverse h2); congr (_ * _).
rewrite (reindex_inj (@perm_inj _ s)) /=; apply: eq_bigr=> i _.
by rewrite permK.
Qed.

End DualMap.
