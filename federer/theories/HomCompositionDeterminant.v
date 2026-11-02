(** Federer (1969), 2.7.16, example (2), printed pp. 136–137: the
    determinants of the linear maps f |-> g o f and f |-> f o h of Hom(U,
    V). "Using a base e_1, ..., e_m of U we construct a G action preserving
    isomorphism X ~ V^m by mapping f in X onto (f(e_1), ..., f(e_m))": in
    terms of the dual base e_1*, ..., e_m* of U and a base v_1, ..., v_n of
    V, the maps x |-> e_k*(x) v_i form a base of X = Hom(U, V)
    (hom_rank_one_base), and f |-> g o f acts on the k-th copy {x |->
    e_k*(x) v : v in V} of V as g, so that its determinant is (det g)^m
    (hom_left_composition_det). On the right, f |-> f o h acts on the i-th
    copy {x |-> omega(x) w_i : omega in wedge^1 V} of wedge^1 V = Hom(V, R)
    as wedge^1 h, so that its determinant is (det wedge^1 h)^p = (det h)^p
    for p = dim W (hom_right_composition_det); this is the computation
    behind the commutative diagram of p. 137, in which wedge^1 carries right
    multiplication by g^{-1} to left multiplication by (wedge^1 g)^{-1}. The
    rank one map x |-> omega(x) v is hom_with_coefficient v omega, Allard's
    omega . v; vectors and covectors are not identified.  *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import LinearBasis FiniteIndependence FiniteBasisCriterion FiniteBasisComparison FiniteDualDimension
  Annihilator Hom CoefficientCoordinates ExteriorDeterminant BlockDeterminant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section FamilyReindex.
Variable K : fieldType.
Variable X : lmodType K.

(** Source for [reindexed_family_independent]: a family indexed by a
    finite set remains independent after a bijective change of index,
    Federer 1.1.2, p. 10; supporting the base of X ~ V^m of 2.7.16,
    p. 136. Supporting lemma. *)
Lemma reindexed_family_independent (I J : finType) (F : I -> X) (s : J -> I) :
  bijective s -> finite_independent F -> finite_independent (F \o s).
Proof.
move=> hs hF a ha.
have [t hst hts] := hs.
have h0 : \sum_i a (t i) *: F i = 0.
  by rewrite (reindex s (onW_bij _ hs)) /=; under eq_bigr do rewrite hst.
by move=> j; rewrite -(hst j); exact: hF h0 (s j).
Qed.

(** Source for [reindexed_family_spanning]: a spanning family indexed by
    a finite set remains spanning after a bijective change of index,
    Federer 1.1.2, p. 10; supporting 2.7.16, p. 136. Supporting lemma. *)
Lemma reindexed_family_spanning (I J : finType) (F : I -> X) (s : J -> I) :
  bijective s -> (forall x, exists a : I -> K, x = \sum_i a i *: F i) ->
  forall x, exists a : J -> K, x = \sum_j a j *: (F \o s) j.
Proof.
move=> hs hF x; have [a ha] := hF x.
exists (a \o s); rewrite ha (reindex s (onW_bij _ hs)) /=.
by [].
Qed.

(** Source for [enum_val_bijective]: the enumeration of the pairs
    (k, i) through enum_val is a bijection, supporting the base of
    X ~ V^m in Federer 2.7.16, p. 136. Supporting lemma. *)
Lemma enum_val_bijective (I : finType) : bijective (fun j : 'I_#|{: I}| => enum_val j).
Proof. exact: enum_val_bij. Qed.

(** Source for [enumerated_family_basis]: a finite family indexed by
    the pairs (k, i) which is independent and spanning gives a base
    indexed by the ordinals below the number of pairs, through enum_val,
    Federer 1.1.2, p. 10; supporting 2.7.16, p. 136. Supporting lemma. *)
Lemma enumerated_family_basis (I : finType) (F : I -> X) :
  finite_independent F -> (forall x, exists a : I -> K, x = \sum_i a i *: F i) ->
  is_basis (fun j : 'I_#|{: I}| => F (enum_val j)).
Proof.
move=> hi hsp; apply: finite_basis_criterion.
  exact: (reindexed_family_independent (enum_val_bijective I) hi).
exact: (reindexed_family_spanning (enum_val_bijective I) hsp).
Qed.

End FamilyReindex.

Section RankOneMaps.
Variable K : fieldType.
Variables U V : lmodType K.

(** Source for [coefficient_map_fun]: v |-> omega . v, where
    (omega . v)(x) = omega(x) v, Allard's notation for the rank one maps
    of Federer 1.4.5, p. 21, used for the isomorphism X ~ V^m of 2.7.16,
    p. 136. Definition of the function. *)
Definition coefficient_map_fun (omega : Hom U K^o) (v : V) : Hom U V := hom_with_coefficient v omega.

(** Source for [coefficient_map_linear]: v |-> omega . v is linear,
    Federer 1.4.5, p. 21, and 2.7.16, p. 136. Supporting lemma. *)
Lemma coefficient_map_linear (omega : Hom U K^o) : linear (coefficient_map_fun omega).
Proof.
move=> a v w; apply: hom_ext=> x.
by rewrite hom_addE hom_scaleE /coefficient_map_fun !hom_with_coefficientE scalerDr !scalerA mulrC.
Qed.
HB.instance Definition _ (omega : Hom U K^o) := GRing.isLinear.Build K V (Hom U V) *:%R
  (coefficient_map_fun omega) (coefficient_map_linear omega).

(** Source for [coefficient_map]: the linear map v |-> omega . v of V
    into Hom(U, V), Federer 1.4.5, p. 21; the k-th copy of V in
    X ~ V^m, 2.7.16, p. 136, is its image for omega = e_k*. Definition. *)
Definition coefficient_map (omega : Hom U K^o) : {linear V -> Hom U V} :=
  GRing.Linear.clone _ _ _ _ (coefficient_map_fun omega) _.

(** Source for [coefficient_covector_linear]: omega |-> omega . w is
    linear, Federer 1.4.5, p. 21; the i-th copy of wedge^1 U in
    Hom(U, V), 2.7.16, p. 137, is its image. Supporting lemma. *)
Lemma coefficient_covector_linear (w : V) : linear (@hom_with_coefficient K U V w).
Proof. exact: hom_postcompose_linear. Qed.
HB.instance Definition _ (w : V) := GRing.isLinear.Build K (Hom U K^o) (Hom U V) *:%R
  (@hom_with_coefficient K U V w) (coefficient_covector_linear w).

(** Source for [coefficient_covector_map]: the linear map
    omega |-> omega . w of wedge^1 U = Hom(U, R) into Hom(U, V),
    Federer 1.4.5, p. 21, and 2.7.16, p. 137. Definition. *)
Definition coefficient_covector_map (w : V) : {linear Hom U K^o -> Hom U V} :=
  GRing.Linear.clone _ _ _ _ (@hom_with_coefficient K U V w) _.

Variables m n : nat.
Variable c : 'I_m -> U.
Hypothesis hc : is_basis c.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.

(** Source for [rank_one_pairs]: the maps x |-> e_k*(x) v_i, indexed by
    the pairs (k, i), corresponding to the base of V^m under the
    isomorphism X ~ V^m of Federer 2.7.16, p. 136. Definition. *)
Definition rank_one_pairs (x : ('I_m * 'I_n)%type) : Hom U V :=
  hom_with_coefficient (b x.2) (dual_basis hc x.1).

(** Source for [rank_one_pairs_independent]: the maps x |-> e_k*(x) v_i
    are independent, Federer 1.1.2 and 1.4.5, pp. 10 and 21: evaluation
    at e_l of a vanishing combination gives sum_i a_{l,i} v_i = 0.
    Supporting lemma for 2.7.16, p. 136. *)
Lemma rank_one_pairs_independent : finite_independent rank_one_pairs.
Proof.
move=> a ha [l i].
have hl : (\sum_x a x *: rank_one_pairs x : Hom U V) (c l) = 0 by rewrite ha hom_zeroE.
have hl' : \sum_(k < m) \sum_(j < n) (if k == l then a (k, j) else 0) *: b j = 0.
  rewrite pair_bigA /= -[RHS]hl hom_sum_coefficientsE; apply: eq_bigr=> -[k j] _.
  rewrite hom_scaleE /rank_one_pairs hom_with_coefficientE dual_basisE /=.
  by case: (eqVneq k l)=> [->|hkl]; rewrite ?scale1r // !scale0r scaler0.
have he : \sum_(j < n) a (l, j) *: b j = 0.
  rewrite -[RHS]hl' (bigD1 l) //= [X in _ + X]big1 ?addr0.
    by apply: eq_bigr=> j _; rewrite eqxx.
  by move=> k hk; apply: big1=> j _; rewrite (negbTE hk) scale0r.
exact: (finite_basis_independent hb he i).
Qed.

(** Source for [rank_one_pairs_spanning]: every f in Hom(U, V) is
    sum_{k,i} v_i*(f(e_k)) (x |-> e_k*(x) v_i), Federer 1.4.5, p. 21,
    expanding f = sum_k (x |-> e_k*(x) f(e_k)); supporting 2.7.16,
    p. 136. Supporting lemma. *)
Lemma rank_one_pairs_spanning (f : Hom U V) :
  exists a : ('I_m * 'I_n)%type -> K, f = \sum_x a x *: rank_one_pairs x.
Proof.
exists (fun x => (dual_basis hb x.2 (f (c x.1)) : K)).
transitivity (\sum_(k < m) \sum_(i < n) (dual_basis hb i (f (c k)) : K) *: rank_one_pairs (k, i)).
  rewrite [LHS](finite_Hom_coefficients hc f); apply: eq_bigr=> k _.
  rewrite [in LHS](basis_vector_expansion hb (f (c k))).
  transitivity (coefficient_map (dual_basis hc k) (\sum_i (dual_basis hb i (f (c k)) : K) *: b i));
    first by [].
  rewrite (linear_sum (coefficient_map (dual_basis hc k))); apply: eq_bigr=> i _.
  by rewrite linearZ.
by rewrite pair_bigA; apply: eq_bigr=> -[k i].
Qed.

(** Source for [hom_rank_one_base]: the base x |-> e_k*(x) v_i of
    X = Hom(U, V), corresponding to the base of V^m under the
    isomorphism X ~ V^m of Federer 2.7.16, p. 136; indexed through
    enum_val by the ordinals below #|'I_m x 'I_n|. Definition. *)
Definition hom_rank_one_base : 'I_#|{: 'I_m * 'I_n}| -> Hom U V :=
  block_family b (fun k => coefficient_map (dual_basis hc k)).

(** Source for [hom_rank_one_baseP]: hom_rank_one_base is a base of
    Hom(U, V), Federer 1.1.2, p. 10, and 2.7.16, p. 136. Supporting
    lemma. *)
Lemma hom_rank_one_baseP : is_basis hom_rank_one_base.
Proof.
exact: (enumerated_family_basis rank_one_pairs_independent rank_one_pairs_spanning).
Qed.

(** Source for [hom_dual_rank_one_base]: the base x |-> v_k*(x) w_i of
    Hom(V, W) indexed by the pairs (i, k), i for the base w of the
    target and k for the dual base of V, the copies of wedge^1 V in
    Federer 2.7.16, p. 137. Definition (here with U, V in place of
    V, W). *)
Definition hom_dual_rank_one_base : 'I_#|{: 'I_n * 'I_m}| -> Hom U V :=
  block_family (dual_basis hc) (fun i => coefficient_covector_map (b i)).

(** Source for [hom_dual_rank_one_baseP]: hom_dual_rank_one_base is a
    base of Hom(U, V), the same maps as hom_rank_one_base with the pairs
    reversed, Federer 1.1.2, p. 10, and 2.7.16, p. 137. Supporting
    lemma. *)
Lemma hom_dual_rank_one_baseP : is_basis hom_dual_rank_one_base.
Proof.
have hs : bijective (fun x : ('I_n * 'I_m)%type => (x.2, x.1)).
  by exists (fun x : ('I_m * 'I_n)%type => (x.2, x.1)); case.
apply: (@enumerated_family_basis K (Hom U V) _ (rank_one_pairs \o (fun x : ('I_n * 'I_m)%type => (x.2, x.1)))).
  exact: reindexed_family_independent hs rank_one_pairs_independent.
exact: reindexed_family_spanning hs rank_one_pairs_spanning.
Qed.

End RankOneMaps.

Section CompositionMaps.
Variable K : fieldType.
Variables U V W : lmodType K.

(** Source for [hom_left_composition_fun]: the map f |-> g o f of
    Hom(U, V) into itself, the action of the linear group of V on
    X = Hom(U, V) "by functional composition", Federer 2.7.16, p. 136.
    Definition of the function. *)
Definition hom_left_composition_fun (g : Hom V V) (f : Hom U V) : Hom U V := hom_comp g f.

HB.instance Definition _ (g : Hom V V) := GRing.isLinear.Build K (Hom U V) (Hom U V) *:%R
  (hom_left_composition_fun g) (hom_postcompose_linear g).

(** Source for [hom_left_composition]: f |-> g o f as a linear
    endomorphism of Hom(U, V), Federer 2.7.16, p. 136. Definition. *)
Definition hom_left_composition (g : Hom V V) : {linear Hom U V -> Hom U V} :=
  GRing.Linear.clone _ _ _ _ (hom_left_composition_fun g) _.

(** Source for [hom_right_composition_fun]: the map f |-> f o h of
    Hom(V, W) into itself, right multiplication in case W = V, Federer
    2.7.16, p. 137. Definition of the function. *)
Definition hom_right_composition_fun (h : Hom V V) (f : Hom V W) : Hom V W := hom_comp f h.

HB.instance Definition _ (h : Hom V V) := GRing.isLinear.Build K (Hom V W) (Hom V W) *:%R
  (hom_right_composition_fun h) (hom_precompose_linear h).

(** Source for [hom_right_composition]: f |-> f o h as a linear
    endomorphism of Hom(V, W), Federer 2.7.16, p. 137. Definition. *)
Definition hom_right_composition (h : Hom V V) : {linear Hom V W -> Hom V W} :=
  GRing.Linear.clone _ _ _ _ (hom_right_composition_fun h) _.

Hypothesis h2 : (1 + 1 : K) != 0.
Variables m n p : nat.
Variable c : 'I_m -> U.
Hypothesis hc : is_basis c.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Variable w : 'I_p -> W.
Hypothesis hw : is_basis w.

(** Source for [hom_left_composition_det]: the determinant of the
    action f |-> g o f of g on X = Hom(U, V) is (det g)^m, m = dim U,
    because under X ~ V^m of Federer 2.7.16, p. 136, g acts on each of
    the m copies of V as g; with det of 1.3.4, p. 16. Supporting
    theorem for "phi is |det|^{-m} covariant". *)
Theorem hom_left_composition_det (g : Hom V V) :
  det h2 (hom_rank_one_baseP hc hb) (hom_left_composition g) =
    det h2 hb (hom_as_linear g) ^+ m.
Proof.
apply: (block_det_power h2 hb (hom_rank_one_baseP hc hb)).
move=> k v; apply: hom_ext=> x.
change (g ((dual_basis hc k x : K) *: v) = (dual_basis hc k x : K) *: g v).
exact: (linearZ_LR (hom_as_linear g)).
Qed.

(** Source for [hom_right_composition_det]: the determinant of
    f |-> f o h on Hom(V, W) is (det h)^p, p = dim W: on each of the p
    copies {x |-> omega(x) w_i} of wedge^1 V it acts as wedge^1 h, and
    det(wedge^1 h) = det h; this is the computation behind the diagram
    of Federer 2.7.16, p. 137, and "|det(wedge^1 g)^{-1}|^{-n} =
    |det g|^n". Supporting theorem. *)
Theorem hom_right_composition_det (h : Hom V V) :
  det h2 (hom_dual_rank_one_baseP hb hw) (hom_right_composition h) =
    det h2 hb (hom_as_linear h) ^+ p.
Proof.
rewrite -(dual_map_det h2 hb (hom_as_linear h)).
apply: (block_det_power h2 (dual_basisP hb) (hom_dual_rank_one_baseP hb hw)).
by move=> i omega; apply: hom_ext=> x.
Qed.

End CompositionMaps.

Arguments hom_left_composition_fun {K} U {V} g f.
Arguments hom_left_composition {K} U {V} g.
Arguments hom_right_composition_fun {K V} W h f.
Arguments hom_right_composition {K V} W h.
