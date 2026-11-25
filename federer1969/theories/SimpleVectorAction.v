(** Federer (1969), 2.7.16, example (4), printed p. 138: "However, the
    action of GL(n, R) on the space of all nonzero simple m vectors of R^n
    admits a |det|^{-m} covariant integral." Federer presupposes the action
    g xi = (wedge_m g) xi (1.3.1, p. 13) and the relative topology of
    wedge_m R^n with the norm of 1.7.5, p. 32. This module supplies the
    action and its continuity. Here V is a space with an inner product and a
    finite basis, wedge_m V carries the inner product exterior_inner_form of
    1.7.5, and the space X of nonzero simple m-vectors is the subtype
    nonzero_simple_set with the relative topology. wedge_m g maps simple
    m-vectors to simple m-vectors and is univalent for g in GL(V).
    Continuity at (g_0, xi_0) with xi_0 simple: |(wedge_m g) xi - (wedge_m
    g_0) xi_0| is at most |(wedge_m g)(xi - xi_0)| + |(wedge_m g) xi_0 -
    (wedge_m g_0) xi_0|; the first term is at most ||g||^m |xi - xi_0|
    (1.7.6, p. 34, exterior_operator_pointwise_bound), and for xi_0 = v_1
    wedge ... wedge v_m the square of the second is a polynomial function of
    g (1.10.4, p. 46), by the permutation formula of 1.7.5 for inner
    products of simple m-vectors, vanishing at g_0. GL(V) acts transitively
    on X: a nonzero simple m-vector is the product of a basis of its
    associated subspace (1.6.1, p. 24), which extends to a basis of V. The
    local erratum has no entry for this passage. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From mathcomp Require Import fingroup perm.
From Federer Require Import RealMetricBackground InnerProductUP InnerProductLaws InnerNorm InnerMetric
  InnerNormedTopology LinearBasis Bilinear InversionCount GradedComponents TensorUP Hom HomInner FiniteDualDimension ModuleQuotient
  SubspaceCarrier GrassmannSubspaces InnerProductRestriction ExteriorGrading ExteriorAlgebra ExteriorMaps
  FiniteExteriorPowers ExteriorMapScaling InnerExterior InnerExteriorProducts InnerExteriorPositivity
  ExteriorNorm OperatorNormUP OperatorNorm ExteriorOperatorEstimate AssociatedSubspace SimpleElementary
  SimpleDimensionCriterion PolynomialFunctions PolynomialContinuity HomMonomorphisms
  HomCompositionDeterminant BasisInterpolation EuclideanLinearMaps IsotropyGroupTopology
  SubtypeCompactHausdorff TopologicalProductMaps TopologicalGroupUP TopologicalGroupLaws
  HomSpaceTopology LinearGroupTopology LinearGroupSealed SubspaceStabiliser AffineGroupTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section WordContinuity.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Variable m : nat.
Local Notation h2 := (euclidean_two_nonzero R).
Local Notation HVV := (inner_metric_space (hom_inner_productP hB hB hb)).
Local Notation L := (inner_metric_space (exterior_inner_productP h2 hB m)).
Local Notation ip := (exterior_inner_form h2 hB (m := m)).

(** Source for [word_image]: the simple m-vector f(v_1) wedge ... wedge
    f(v_m) for f in Hom(V, V), Federer 1.3.1, p. 13, supporting
    2.7.16, p. 138. Definition. *)
Definition word_image (v : 'I_m -> V) (f : Hom V V) : exterior_power V m :=
  e_lambda (fun i => f (v i)) (ord_tuple m).

(** Source for [word_inner_polynomial]: f |-> (f(v_1) wedge ... wedge
    f(v_m)) . (f(w_1) wedge ... wedge f(w_m)) is a polynomial function
    on Hom(V, V), Federer 1.10.4, p. 46, by the permutation formula of
    1.7.5, pp. 31–32. Supporting lemma for 2.7.16, p. 138. *)
Lemma word_inner_polynomial (v w : 'I_m -> V) :
  is_polynomial_function (fun f : Hom V V => (ip (word_image v f) (word_image w f) : R^o)).
Proof.
apply: (polynomial_function_eq (P := fun f : Hom V V =>
  \sum_(s <- index_enum 'S_m) (FedererPermutation.index R s *:
    (foldr *%R 1 [seq (B (f (v (s i))) (f (w i)) : R^o) | i <- enum 'I_m] : R^o)))).
  move=> f; rewrite /word_image (exterior_inner_product_permutations h2 hB).
  by apply: eq_bigr.
apply: polynomial_big_sum=> s.
apply: polynomial_scale.
apply: (@polynomial_foldr_mul R (Hom V V) _ (enum 'I_m)
  (fun i (f : Hom V V) => (B (f (v (s i))) (f (w i)) : R^o))).
move=> i; exact: (hom_inner_values_polynomial hB hb (v (s i)) (w i)).
Qed.

(** Source for [word_fixed_inner_polynomial]: f |-> (f(v_1) wedge ...
    wedge f(v_m)) . (u_1 wedge ... wedge u_m) is a polynomial function
    on Hom(V, V), Federer 1.10.4, p. 46, and 1.7.5, pp. 31–32.
    Supporting lemma for 2.7.16, p. 138. *)
Lemma word_fixed_inner_polynomial (v u : 'I_m -> V) :
  is_polynomial_function (fun f : Hom V V => (ip (word_image v f) (e_lambda u (ord_tuple m)) : R^o)).
Proof.
apply: (polynomial_function_eq (P := fun f : Hom V V =>
  \sum_(s <- index_enum 'S_m) (FedererPermutation.index R s *:
    (foldr *%R 1 [seq (B (f (v (s i))) (u i) : R^o) | i <- enum 'I_m] : R^o)))).
  move=> f; rewrite /word_image (exterior_inner_product_permutations h2 hB).
  by apply: eq_bigr.
apply: polynomial_big_sum=> s.
apply: polynomial_scale.
apply: (@polynomial_foldr_mul R (Hom V V) _ (enum 'I_m)
  (fun i (f : Hom V V) => (B (f (v (s i))) (u i) : R^o))).
move=> i.
exact: (polynomial_linear (GRing.Linear.clone _ _ _ _ (@hom_inner_coordinate R V V B (v (s i)) (u i)) _)).
Qed.

(** Source for [word_image_continuous]: f |-> f(v_1) wedge ... wedge
    f(v_m) is continuous from Hom(V, V) to wedge_m V, Federer 1.7.5,
    p. 32, and 1.10.4, p. 46: |a(f) - a(f_0)|^2 is a polynomial function
    of f vanishing at f_0. Supporting lemma for 2.7.16, p. 138. *)
Lemma word_image_continuous (v : 'I_m -> V) : continuous (fun f : HVV => (word_image v f : L)).
Proof.
move=> f0; apply/(@cvgrPdist_lt _ _ _ (nbhs f0) (nbhs_filter f0))=> eps heps.
pose a0 := word_image v f0.
pose D := fun f : Hom V V => (ip (word_image v f) (word_image v f) - (ip (word_image v f) a0 + ip (word_image v f) a0)
  + ip a0 a0 : R^o).
have hbil := exterior_inner_form_bilinear h2 hB m.
have hsym := exterior_inner_symmetric h2 hB (m := m).
have hDE f : D f = `|(a0 : L) - (word_image v f : L)| ^+ 2.
  rewrite inner_norm_topologyE inner_norm_sqr.
  rewrite (bilBl hbil) !(bilBr hbil) (hsym a0 (word_image v f)) /D.
  by rewrite opprB [in RHS]addrC addrA addrAC opprD addrA.
have hpa := word_inner_polynomial v v.
have hpb := word_fixed_inner_polynomial v (fun i => f0 (v i)).
have hpD : is_polynomial_function (D : Hom V V -> R^o).
  have hQ1 := polynomial_lincomb 1 hpb hpb.
  have hQ2 := polynomial_lincomb (-1) hQ1 hpa.
  have hQ3 := polynomial_lincomb 1 hQ2 (polynomial_constant (Hom V V) (ip a0 a0 : R^o)).
  apply: (polynomial_function_eq _ hQ3)=> f; rewrite /D !scale1r scaleN1r.
  by congr (_ + _); rewrite addrC.
have hDc := @finite_inner_polynomial_continuous R (Hom V V) _ (hom_inner_productP hB hB hb) _ _
  (hom_rank_one_baseP hb hb) _ hpD.
have hD0 : D f0 = 0 by rewrite hDE subrr normr0 expr0n.
have heps2 : 0 < eps ^+ 2 by rewrite exprn_gt0.
have hlt : (fun f : HVV => (D f : R^o)) f0 < eps ^+ 2 by rewrite /= hD0.
have := (@cvgr_lt R HVV (nbhs f0) (nbhs_filter f0) (fun f : HVV => (D f : R^o)) (D f0) (hDc f0) _ hlt).
apply: filterS=> f hf.
have hsq : `|(a0 : L) - (word_image v f : L)| ^+ 2 < eps ^+ 2 by rewrite -hDE.
by rewrite -(ltr_pXn2r (n := 2)) ?nnegrE ?normr_ge0 ?(ltW heps).
Qed.

End WordContinuity.

Section SimpleAction.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Variable m : nat.
Local Notation h2 := (euclidean_two_nonzero R).
Local Notation HVV := (inner_metric_space (hom_inner_productP hB hB hb)).
Local Notation L := (inner_metric_space (exterior_inner_productP h2 hB m)).
Local Notation GL := (set_type (linear_group hB hb)).
Local Notation mul := (linear_group_mul hB hb).
Local Notation inv := (linear_group_inv hB hb).
Local Notation unit := (linear_group_unit hB hb).
Local Notation hG := (linear_group_operations hB hb).
Local Notation onorm := (hom_operator_norm hB hB hb).

(** Source for [hgl]: the group laws of GL(V), used in this section. *)
Let hgl := linear_group_group_laws hG.

(** Source for [exterior_group_map]: wedge_m g for g in GL(n, R), the
    action "of GL(n, R) on the space of all nonzero simple m vectors",
    Federer 2.7.16, p. 138, with wedge_m of 1.3.1, p. 13. Definition. *)
Definition exterior_group_map (g : GL) : {linear exterior_power V m -> exterior_power V m} :=
  exterior_power_map (hom_as_linear (set_val g : Hom V V)) m.

(** Source for [exterior_group_map_mul]: wedge_m(g h) =
    wedge_m g o wedge_m h, Federer 1.3.1, p. 13. Supporting lemma. *)
Lemma exterior_group_map_mul (g h : GL) x :
  exterior_group_map (mul g h) x = exterior_group_map g (exterior_group_map h x).
Proof.
rewrite /exterior_group_map exterior_power_map_composition; apply: exterior_power_map_ext=> v.
by rewrite /= (linear_group_mulE hG) hom_compE.
Qed.

(** Source for [exterior_group_map_unit]: wedge_m 1_V = 1, Federer
    1.3.1, p. 13. Supporting lemma. *)
Lemma exterior_group_map_unit x : exterior_group_map unit x = x.
Proof.
rewrite /exterior_group_map -[RHS](exterior_power_map_identity (m := m)).
by apply: exterior_power_map_ext=> v; rewrite /= (linear_group_unitE hG) hom_identityE.
Qed.

(** Source for [exterior_group_map_inv]: wedge_m(g^{-1}) o wedge_m g =
    1, Federer 1.3.1, p. 13. Supporting lemma. *)
Lemma exterior_group_map_inv (g : GL) x : exterior_group_map (inv g) (exterior_group_map g x) = x.
Proof. by rewrite -exterior_group_map_mul (group_mulVg hgl) exterior_group_map_unit. Qed.

(** Source for [exterior_group_map_injective]: wedge_m g is univalent
    for g in GL(n, R), Federer 1.3.1, p. 13. Supporting lemma. *)
Lemma exterior_group_map_injective (g : GL) : injective (exterior_group_map g).
Proof. by move=> x y hxy; rewrite -(exterior_group_map_inv g x) hxy exterior_group_map_inv. Qed.

(** Source for [exterior_group_map_word]: wedge_m g (v_1 wedge ... wedge
    v_m) = g(v_1) wedge ... wedge g(v_m), Federer 1.3.1, p. 13.
    Supporting lemma. *)
Lemma exterior_group_map_word (g : GL) (v : 'I_m -> V) :
  exterior_group_map g (e_lambda v (ord_tuple m)) = word_image v (set_val g).
Proof. exact: exterior_map_indexed_product. Qed.

(** Source for [exterior_group_map_simple]: wedge_m g maps simple
    m-vectors to simple m-vectors, Federer 1.6.1, p. 23, and 1.3.1,
    p. 13. Supporting lemma. *)
Lemma exterior_group_map_simple (g : GL) x : simple x -> simple (exterior_group_map g x).
Proof.
move=> [t ->]; rewrite /exterior_group_map exterior_map_indexed_product.
exists (map_tuple (set_val g : Hom V V) t).
apply: (@val_inj _ _ _ (e_lambda (fun i => (set_val g : Hom V V) (idfun i)) t)).
change (component_val (e_lambda (fun i => (set_val g : Hom V V) (idfun i)) t) =
  component_val (e_lambda idfun (map_tuple (set_val g : Hom V V) t))).
by rewrite !e_lambdaE /= map_id.
Qed.

(** Source for [nonzero_simple_set]: "the space of all nonzero simple m
    vectors of R^n", Federer 2.7.16, p. 138, as a subset of wedge_m V
    (1.6.1, p. 23). Definition. *)
Definition nonzero_simple_set : set L := [set x | x != 0 /\ simple x].

Local Notation X := (set_type nonzero_simple_set).

(** Source for [exterior_group_map_nonzero_simple]: wedge_m g maps
    nonzero simple m-vectors to nonzero simple m-vectors, Federer
    2.7.16, p. 138. Supporting lemma. *)
Lemma exterior_group_map_nonzero_simple (g : GL) x :
  nonzero_simple_set x -> nonzero_simple_set (exterior_group_map g x).
Proof.
move=> [hx hs]; split; last exact: exterior_group_map_simple.
move: hx; apply: contra_neq=> h0.
by rewrite -(exterior_group_map_inv g x) h0 linear0.
Qed.

(** Source for [simple_vector_action]: "the action of GL(n, R) on the
    space of all nonzero simple m vectors", Federer 2.7.16, p. 138:
    A(g, xi) = (wedge_m g) xi. Definition. *)
Definition simple_vector_action (g : GL) (x : X) : X :=
  exist _ (exterior_group_map g (set_val x)) (mem_set (exterior_group_map_nonzero_simple g (set_valP x))).

(** Source for [simple_vector_actionE]: the value (wedge_m g) xi,
    Federer 2.7.16, p. 138. Supporting lemma. *)
Lemma simple_vector_actionE (g : GL) (x : X) : set_val (simple_vector_action g x) = exterior_group_map g (set_val x).
Proof. by []. Qed.

(** Source for [exterior_group_map_bound]: |(wedge_m g) xi| <=
    ||g||^m |xi|, Federer 1.7.6, p. 34. Supporting lemma. *)
Lemma exterior_group_map_bound (g : GL) (x : L) :
  `|(exterior_group_map g x : L)| <= onorm (set_val g) ^+ m * `|x|.
Proof.
rewrite !inner_norm_topologyE.
exact: (exterior_operator_pointwise_bound h2 hb (linear_operator_normP hB hB hb (hom_as_linear (set_val g : Hom V V))) x).
Qed.

(** Source for [exterior_action_continuous_at]: (g, xi) |->
    (wedge_m g) xi is continuous at (g_0, xi_0) for simple xi_0,
    Federer 2.7.1, p. 121, for the action of 2.7.16, p. 138:
    |(wedge_m g) xi - (wedge_m g_0) xi_0| <= ||g||^m |xi - xi_0| +
    |(wedge_m g) xi_0 - (wedge_m g_0) xi_0|. Supporting lemma. *)
Lemma exterior_action_continuous_at (g0 : GL) (x0 : L) :
  simple x0 -> {for (g0, x0), continuous (fun q : GL * L => (exterior_group_map q.1 q.2 : L))}.
Proof.
move=> [t ht].
pose v := tnth t.
have hx0 : x0 = e_lambda v (ord_tuple m) by rewrite ht tuple_product.
apply/(@cvgrPdist_lt _ _ _ (nbhs (g0, x0)) (nbhs_filter _))=> eps heps.
pose c := onorm (set_val g0) + 1.
have hc : 0 < c by apply: ltr_wpDl; [exact: hom_operator_norm_nonnegative|exact: ltr01].
have hcm : 0 < c ^+ m by rewrite exprn_gt0.
have heps2 : 0 < eps / 2 by rewrite divr_gt0.
have hr : 0 < eps / 2 / c ^+ m by rewrite divr_gt0.
have hval := @set_type_val_continuous HVV (linear_group hB hb) g0.
have hwc : continuous (fun f : HVV => (word_image v f : L)) := @word_image_continuous R V B hB n b hb m v.
have hw := hwc (set_val g0 : HVV).
have hN1 : nbhs g0 [set g : GL | `|(word_image v (set_val g0) : L) - word_image v (set_val g)| < eps / 2].
  exact: ((proj1 (@cvgrPdist_lt _ L _ (nbhs g0) (nbhs_filter g0) (fun g : GL => (word_image v (set_val g) : L))
    (word_image v (set_val g0)))) (continuous_comp hval hw) (eps / 2) heps2).
have hN2 : nbhs g0 [set g : GL | onorm (set_val g - set_val g0) < 1].
  exact: (hval _ (hom_space_operator_ball_nbhs (set_val g0 : HVV) ltr01)).
exists ([set g : GL | `|(word_image v (set_val g0) : L) - word_image v (set_val g)| < eps / 2 /\
    onorm (set_val g - set_val g0) < 1], ball x0 (eps / 2 / c ^+ m)).
  by split; [exact: filterI|exact: nbhsx_ballx].
move=> [g x] [/= [hg1 hg2] hx]; rewrite -ball_normE /= in hx.
have hgn : onorm (set_val g) <= c.
  apply: le_trans (hom_operator_norm_sub_bound hB hB hb (set_val g0) (set_val g)) _.
  by rewrite lerD2l ltW.
have hgm : onorm (set_val g) ^+ m <= c ^+ m.
  by rewrite lerXn2r ?nnegrE ?hom_operator_norm_nonnegative ?(ltW hc).
have he : (exterior_group_map g0 x0 : L) - exterior_group_map g x =
    ((word_image v (set_val g0) : L) - word_image v (set_val g)) + exterior_group_map g (x0 - x).
  rewrite linearB hx0 !exterior_group_map_word.
  by rewrite addrA subrK.
rewrite he; apply: le_lt_trans (ler_normD _ _) _.
rewrite (splitr eps); apply: ltr_leD=> //.
apply: le_trans (exterior_group_map_bound g (x0 - x)) _.
apply: (@le_trans _ _ (c ^+ m * (eps / 2 / c ^+ m))); last by rewrite mulrC divfK ?gt_eqF.
by apply: ler_pM; rewrite ?exprn_ge0 ?hom_operator_norm_nonnegative ?normr_ge0 // ltW.
Qed.

(** Source for [simple_vector_action_continuous]: the action of
    GL(n, R) on the nonzero simple m-vectors is continuous, Federer
    2.7.1, p. 121, for 2.7.16, p. 138. Supporting lemma. *)
Lemma simple_vector_action_continuous : continuous (fun q : GL * X => simple_vector_action q.1 q.2).
Proof.
apply: set_type_continuous_into=> q.
have hp : continuous (fun q : GL * X => (q.1, (set_val q.2 : L))).
  apply: (@topological_pair_continuous (GL * X)%type GL L); first exact: first_projection_continuous.
  move=> r; apply: (@continuous_comp (GL * X)%type X L (@snd GL X) set_val r).
    exact: second_projection_continuous.
  exact: set_type_val_continuous.
have hq : {for (q.1, (set_val q.2 : L)), continuous (fun r : GL * L => (exterior_group_map r.1 r.2 : L))}.
  exact: (@exterior_action_continuous_at q.1 (set_val q.2) (set_valP q.2).2).
exact: (@continuous_comp (GL * X)%type (GL * L)%type L (fun q : GL * X => (q.1, (set_val q.2 : L)))
  (fun r : GL * L => (exterior_group_map r.1 r.2 : L)) q (hp q) hq).
Qed.

(** Source for [simple_vector_action_compatible]: A(gh, xi) =
    A(g, A(h, xi)), Federer 2.7.1, p. 121. Supporting lemma. *)
Lemma simple_vector_action_compatible (g h : GL) (x : X) :
  simple_vector_action (mul g h) x = simple_vector_action g (simple_vector_action h x).
Proof. by apply: val_inj; rewrite /= exterior_group_map_mul. Qed.

(** Source for [nonzero_simple_frame]: a nonzero simple m-vector is
    the product of a basis of its associated subspace, Federer 1.6.1,
    p. 24 (simple_is_basis_product). Supporting lemma. *)
Lemma nonzero_simple_frame (x : L) : nonzero_simple_set x ->
  exists (W : subspace V) (w : 'I_m -> subspace_space W),
    is_basis w /\ x = e_lambda (fun i => subspace_val (w i)) (ord_tuple m).
Proof.
move=> [hx hs]; have [w [hw he]] := simple_is_basis_product h2 hx hs.
by exists (FedererSimple.T x), w.
Qed.

(** Source for [simple_vector_action_transitive]: GL(n, R) acts
    transitively on the nonzero simple m-vectors, Federer 2.7.16,
    p. 138: bases of the associated subspaces extend to bases of V
    (1.6.1, p. 23), and the linear map carrying one basis to the other
    carries one product to the other. Supporting lemma. *)
Lemma simple_vector_action_transitive (x y : X) : exists g, simple_vector_action g x = y.
Proof.
have [W1 [w1 [hw1 hx]]] := nonzero_simple_frame (set_valP x).
have [W2 [w2 [hw2 hy]]] := nonzero_simple_frame (set_valP y).
have [E1 [hE1 hE1w]] := adapted_basis_exists hb hw1.
have [E2 [hE2 hE2w]] := adapted_basis_exists hb hw2.
pose f := basis_interpolation hE1 E2.
pose f' := basis_interpolation hE2 E1.
have hff : forall v, f' (f v) = v.
  apply: (basis_linear_ext hE1 (linear_comp f' f) (linear_id V))=> j.
  change (f' (f (E1 j)) = E1 j).
  by rewrite /f basis_interpolationE /f' basis_interpolationE.
have hfi : injective f by move=> u v huv; rewrite -(hff u) huv hff.
have hfG : linear_group hB hb (hom_of_linear f : HVV) by move=> u v; rewrite !hom_of_linearE; exact: hfi.
exists (exist _ (hom_of_linear f : HVV) (mem_set hfG)); apply: val_inj.
change (exterior_group_map (exist _ (hom_of_linear f : HVV) (mem_set hfG)) (set_val x) = set_val y).
rewrite !set_valE hx hy exterior_group_map_word /word_image.
apply: (congr1 (fun e : 'I_m -> V => e_lambda e (ord_tuple m))).
apply: funext=> i; rewrite -hE1w -hE2w.
exact: basis_interpolationE.
Qed.

(** Source for [simple_vector_space_hausdorff]: the space of nonzero
    simple m-vectors is Hausdorff, Federer 2.7.1, p. 121. Supporting
    lemma. *)
Lemma simple_vector_space_hausdorff : hausdorff_space X.
Proof.
apply: set_type_hausdorff.
exact: (@inner_space_hausdorff R (exterior_power V m) _ (exterior_inner_productP h2 hB m)).
Qed.

End SimpleAction.

Arguments exterior_group_map {R V B} hB {n b} hb m g.
Arguments nonzero_simple_set {R V B} hB m x.
Arguments simple_vector_action {R V B} hB {n b} hb m g x.
