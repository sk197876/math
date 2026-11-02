(** Federer (1969), 2.7.16, printed p. 139, example (6): "In particular we
    thus obtain the O(n) invariant measures theta_{n,m} over O(n, m),
    theta*_{n,m} over O*(n, m)". O(n, m) is the set of orthogonal injections
    of R^m into R^n (1.7.2, p. 28) and O*(n, m) the set of orthogonal
    projections of R^n onto R^m, the adjoints of the members of O(n, m)
    (1.7.4, p. 30). Federer does not describe the topologies or the actions;
    this module supplies them. Here U and V are spaces with inner products C
    and B and finite bases c and b (U = R^m, V = R^n). O(U, V) is a subset
    of Hom(U, V) and O*(V, U) a subset of Hom(V, U), each with the relative
    topology of the inner product of 1.7.9, p. 35 (HomSpaceTopology.v). The
    orthogonal group O(V) acts on O(U, V) by A(g, f) = g o f and on O*(V, U)
    by A(g, p) = p o g^{-1}; these are the actions under which theta_{n,m}
    and theta*_{n,m} are invariant in Federer's use in 2.7.16(6)-(7), pp.
    139-140 (for instance "the invariance of theta*_{n,m} implies the
    integrals corresponding to xi and (Lambda_m g) xi are equal"), and they
    correspond under f |-> f*, since (g o f)* = f* o g^{-1} for g in O(V).
    Both actions are continuous and transitive: for f_1, f_2 in O(U, V) an
    orthonormal basis e of U is carried to the orthonormal families f_1(e),
    f_2(e) of V, which extend to orthonormal bases d_1, d_2 of V (1.7.3, p.
    30), and the linear map g with g(d_1) = d_2 is orthogonal with g o f_1 =
    f_2. By the general result for compact groups
    (CompactGroupHomogeneousMeasures.v) O(U, V) and O*(V, U) are compact
    homogeneous spaces of O(V) in the sense of 2.7.1, p. 121. The
    composition of linear maps is continuous on Hom(V, W) x Hom(U, V), by
    the estimate ||f o g|| <= ||f|| ||g|| of 2.7.16, p. 134.  The local erratum has no entry
    for p. 139. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module ring.
From Federer Require Import InnerProductUP InnerNorm InnerMetric InnerNormedTopology LinearBasis
  FiniteIndependence FiniteBasisCriterion FiniteBasisComparison FiniteDimension TensorUP Hom
  HomInner OrthogonalMaps OrthonormalFamilies OrthonormalisationUP GramSchmidt
  OrthonormalCapacityExtension OrthogonalBasisCriteria BasisInterpolation AdjointUP AdjointLaws
  SubtypeCompactHausdorff IsotropyGroupTopology TopologicalProductMaps TopologicalGroupUP
  TopologicalGroupLaws HomogeneousSpaceUP HomSpaceTopology LinearGroupTopology LinearGroupSealed
  OrthogonalGroupTopology MeasurePushforward OrthogonalGroupHaarMeasure CompactGroupHaarNormalisation
  CompactGroupHomogeneousMeasures.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section HomComposition.
Variable R : realType.
Variables U V W : lmodType R.
Variables (A : U -> U -> R) (B : V -> V -> R) (C : W -> W -> R).
Hypotheses (hA : is_inner_product A) (hB : is_inner_product B) (hC : is_inner_product C).
Variables (m : nat) (c : 'I_m -> U) (n : nat) (b : 'I_n -> V).
Hypotheses (hc : is_basis c) (hb : is_basis b).
Local Notation HUV := (inner_metric_space (hom_inner_productP hA hB hc)).
Local Notation HVW := (inner_metric_space (hom_inner_productP hB hC hb)).
Local Notation HUW := (inner_metric_space (hom_inner_productP hA hC hc)).
Local Notation nUV := (hom_operator_norm hA hB hc).
Local Notation nVW := (hom_operator_norm hB hC hb).
Local Notation nUW := (hom_operator_norm hA hC hc).

(** Source for [hom_operator_norm_comp_general]: "||f o g|| <= ||f|| .
    ||g||", Federer 2.7.16, p. 134, for f in Hom(V, W) and g in
    Hom(U, V). Supporting lemma. *)
Lemma hom_operator_norm_comp_general (f : Hom V W) (g : Hom U V) :
  nUW (hom_comp f g) <= nVW f * nUV g.
Proof.
apply: hom_operator_norm_least.
  by rewrite mulr_ge0 // hom_operator_norm_nonnegative.
move=> x; rewrite hom_compE.
apply: le_trans (hom_operator_norm_bound hB hC hb f (g x)) _.
rewrite -mulrA ler_wpM2l ?hom_operator_norm_nonnegative //.
exact: hom_operator_norm_bound.
Qed.

(** Source for [hom_composition_continuous_general]: "composition of
    linear maps is a continuous operation because f o g - h o k =
    (f - h) o g + h o (g - k), ||f o g|| <= ||f|| . ||g||", Federer
    2.7.16, p. 134, for composition Hom(V, W) x Hom(U, V) -> Hom(U, W).
    Supporting theorem, generalising hom_composition_continuous. *)
Theorem hom_composition_continuous_general :
  continuous (fun p : HVW * HUV => (hom_comp (p.1 : Hom V W) (p.2 : Hom U V) : HUW)).
Proof.
move=> [f g] S /hom_space_nbhs_operator [r hr hS].
pose k := nVW f + nUV g + 1.
have hk : 0 < k.
  by apply: ltr_wpDl; [rewrite addr_ge0 ?hom_operator_norm_nonnegative|exact: ltr01].
pose d := Num.min 1 (r / k).
have hd : 0 < d by rewrite /d lt_min ltr01 divr_gt0.
have hd1 : d <= 1 by rewrite /d ge_min lexx.
have hdk : d * k <= r by rewrite -ler_pdivlMr // /d ge_min lexx orbT.
exists ([set h : HVW | nVW (h - f) < d], [set q : HUV | nUV (q - g) < d]).
  by split; exact: hom_space_operator_ball_nbhs.
move=> [h q] [/= hh hq]; apply: hS.
have he : (hom_comp (h : Hom V W) q : HUW) - hom_comp (f : Hom V W) g =
    hom_comp (h - f : HVW) q + hom_comp (f : Hom V W) (q - g : HUV).
  apply: hom_ext=> x; rewrite hom_addE !hom_compE.
  have -> : ((hom_comp (h : Hom V W) q : HUW) - hom_comp (f : Hom V W) g : Hom U W) x =
    h (q x) - f (g x) by [].
  have -> : ((h - f : HVW) : Hom V W) (q x) = h (q x) - f (q x) by [].
  have -> : ((q - g : HUV) : Hom U V) x = q x - g x by [].
  rewrite (linearB (hom_as_linear f)) /=.
  by rewrite addrA subrK.
rewrite he; apply: le_lt_trans (hom_operator_norm_add hA hC hc _ _) _.
have hqn : nUV q <= nUV g + 1.
  apply: le_trans (hom_operator_norm_sub_bound hA hB hc g q) _; rewrite lerD2l.
  exact: le_trans (ltW hq) hd1.
apply: (@lt_le_trans _ _ (d * k)); last exact: hdk.
apply: (@le_lt_trans _ _ (nVW (h - f) * (nUV g + 1) + nVW f * nUV (q - g))).
  apply: lerD; first apply: le_trans (hom_operator_norm_comp_general _ _) _.
    by rewrite ler_wpM2l ?hom_operator_norm_nonnegative.
  exact: hom_operator_norm_comp_general.
rewrite (_ : d * k = d * (nUV g + 1) + d * nVW f); last by rewrite /k; ring.
have hg1 : 0 < nUV g + 1.
  by apply: ltr_wpDl; [exact: hom_operator_norm_nonnegative|exact: ltr01].
apply: ltr_leD; first by rewrite ltr_pM2r.
by rewrite mulrC ler_wpM2r ?hom_operator_norm_nonnegative // ltW.
Qed.

End HomComposition.

Section OrthogonalTransitivity.
Variable R : realType.
Variables U V : lmodType R.
Variables (C : U -> U -> R) (B : V -> V -> R).
Hypotheses (hC : is_inner_product C) (hB : is_inner_product B).
Variables (m : nat) (c : 'I_m -> U) (n : nat) (b : 'I_n -> V).
Hypotheses (hc : is_basis c) (hb : is_basis b).

(** Source for [orthonormal_dimension_bound]: an orthonormal k-family in
    V has k <= dim V, Federer 1.7.1, p. 28; supporting "O(n, m)" with
    n >= m, 1.7.2, p. 28. Supporting lemma. *)
Lemma orthonormal_dimension_bound k (e : 'I_k -> V) : orthonormal_family B e -> (k <= n)%N.
Proof.
move=> he.
have h := @finite_independent_dimension R (finite_basis_vect hb) k e
  (@orthonormal_independent R V B hB (Finite.clone 'I_k _) e he).
by rewrite finite_basis_dimension card_ord in h.
Qed.

(** Source for [orthonormal_family_full_basis]: an orthonormal family of
    dim V vectors is a basis of V, Federer 1.7.1, p. 28. Supporting
    lemma. *)
Lemma orthonormal_family_full_basis (d : 'I_n -> V) : orthonormal_family B d -> is_basis d.
Proof.
move=> hd; apply: (@finite_independent_basis R (finite_basis_vect hb) n d).
  by rewrite finite_basis_dimension card_ord.
exact: (@orthonormal_independent R V B hB (Finite.clone 'I_n _) d hd).
Qed.

(** Source for [orthogonal_injection_transitive]: O(n) acts
    transitively on O(n, m), Federer 2.7.16, p. 139: for orthogonal
    injections f_1, f_2 of U into V there is an orthogonal g of V with
    g o f_1 = f_2. Proof supplied: the orthonormal families f_1(e),
    f_2(e), for an orthonormal basis e of U (1.7.1, p. 28), extend to
    orthonormal bases d_1, d_2 of V (1.7.3, p. 30), and g(d_1) = d_2. *)
Theorem orthogonal_injection_transitive (f1 f2 : {linear U -> V}) :
  is_orthogonal_map C B f1 -> is_orthogonal_map C B f2 ->
  exists g : {linear V -> V}, is_orthogonal_map B B g /\ forall u, g (f1 u) = f2 u.
Proof.
move=> h1 h2.
have [e [he hgs]] := orthonormal_basis_exists hC hc.
have heo := orthonormalisation_orthonormal hgs.
have ho1 := orthogonal_map_orthonormal h1 heo.
have ho2 := orthogonal_map_orthonormal h2 heo.
have hmn := orthonormal_dimension_bound ho1.
have hbi := finite_basis_independent hb.
have [d1 [hd1 hd1e]] := orthonormal_capacity_extension hB hbi ho1 hmn.
have [d2 [hd2 hd2e]] := orthonormal_capacity_extension hB hbi ho2 hmn.
have hd1b := orthonormal_family_full_basis hd1.
have hgd k : basis_interpolation hd1b d2 (d1 k) = d2 k := basis_interpolationE hd1b d2 k.
exists (basis_interpolation hd1b d2); split.
  apply: (orthogonal_map_basis_criterion hB hB hd1b hd1)=> i j.
  by apply: (eq_trans _ (hd2 i j)); congr B; exact: hgd.
apply: (basis_linear_ext he (linear_comp (basis_interpolation hd1b d2) f1) f2)=> i.
rewrite /linear_comp /= -hd1e; apply: (eq_trans (hgd _)); exact: hd2e.
Qed.

End OrthogonalTransitivity.

Section InjectionSpaces.
Variable R : realType.
Variables U V : lmodType R.
Variables (C : U -> U -> R) (B : V -> V -> R).
Hypotheses (hC : is_inner_product C) (hB : is_inner_product B).
Variables (m : nat) (c : 'I_m -> U) (n : nat) (b : 'I_n -> V).
Hypotheses (hc : is_basis c) (hb : is_basis b).
Local Notation HUV := (inner_metric_space (hom_inner_productP hC hB hc)).
Local Notation HVU := (inner_metric_space (hom_inner_productP hB hC hb)).
Local Notation HVV := (inner_metric_space (hom_inner_productP hB hB hb)).
Local Notation O := (orthogonal_group hB hb).
Local Notation om := (@orthogonal_element_map R V B hB n b hb).

(** Source for [orthogonal_injections]: "O(n, m)", Federer 2.7.16,
    p. 139, the orthogonal injections of R^m into R^n (1.7.2, p. 28), as
    a subset of Hom(R^m, R^n). Definition for U and V. *)
Definition orthogonal_injections : set HUV :=
  [set f | is_orthogonal_map C B (hom_as_linear (f : Hom U V))].

(** Source for [orthogonal_projections]: "O*(n, m)", Federer 2.7.16,
    p. 139, the orthogonal projections of R^n onto R^m, the adjoints of
    the members of O(n, m) (1.7.4, p. 30), as a subset of
    Hom(R^n, R^m). Definition for V and U, by is_orthogonal_projection. *)
Definition orthogonal_projections : set HVU :=
  [set p | is_orthogonal_projection B C (hom_as_linear (p : Hom V U))].

Local Notation OI := (set_type orthogonal_injections).
Local Notation OP := (set_type orthogonal_projections).

(** Source for [orthogonal_injection_map]: a member of O(n, m) as a map,
    Federer 2.7.16, p. 139. Definition. *)
Definition orthogonal_injection_map (f : OI) : Hom U V := set_val f.

(** Source for [orthogonal_projection_map]: a member of O*(n, m) as a
    map, Federer 2.7.16, p. 139. Definition. *)
Definition orthogonal_projection_map (p : OP) : Hom V U := set_val p.

(** Source for [orthogonal_injection_map_orthogonal]: each member of
    O(n, m) is an orthogonal injection, Federer 1.7.2, p. 28.
    Supporting lemma. *)
Lemma orthogonal_injection_map_orthogonal (f : OI) :
  is_orthogonal_map C B (hom_as_linear (orthogonal_injection_map f)).
Proof. exact: (set_valP f). Qed.

(** Source for [orthogonal_projection_map_projection]: each member of
    O*(n, m) is an orthogonal projection, Federer 1.7.4, p. 30.
    Supporting lemma. *)
Lemma orthogonal_projection_map_projection (p : OP) :
  is_orthogonal_projection B C (hom_as_linear (orthogonal_projection_map p)).
Proof. exact: (set_valP p). Qed.

(** Source for [orthogonal_injection_of]: an orthogonal injection f of U
    into V as a point of O(n, m), Federer 2.7.16, p. 139. Definition. *)
Definition orthogonal_injection_of (f : {linear U -> V}) (hf : is_orthogonal_map C B f) : OI :=
  exist _ (hom_of_linear f : HUV) (mem_set (hf : orthogonal_injections (hom_of_linear f : HUV))).

(** Source for [orthogonal_projection_of]: an orthogonal projection p of
    V onto U as a point of O*(n, m), Federer 2.7.16, p. 139.
    Definition. *)
Definition orthogonal_projection_of (p : {linear V -> U}) (hp : is_orthogonal_projection B C p) :
    OP :=
  exist _ (hom_of_linear p : HVU) (mem_set (hp : orthogonal_projections (hom_of_linear p : HVU))).

(** Source for [orthogonal_injection_ext]: a point of O(n, m) is
    determined by its values, Federer 2.7.16, p. 139. Supporting lemma. *)
Lemma orthogonal_injection_ext (f g : OI) :
  (forall u, orthogonal_injection_map f u = orthogonal_injection_map g u) -> f = g.
Proof. by move=> h; apply: val_inj; apply: hom_ext. Qed.

(** Source for [orthogonal_projection_ext]: a point of O*(n, m) is
    determined by its values, Federer 2.7.16, p. 139. Supporting lemma. *)
Lemma orthogonal_projection_ext (p q : OP) :
  (forall v, orthogonal_projection_map p v = orthogonal_projection_map q v) -> p = q.
Proof. by move=> h; apply: val_inj; apply: hom_ext. Qed.

(** Source for [orthogonal_injection_action_member]: g o f is an
    orthogonal injection for g in O(n) and f in O(n, m), Federer 1.7.2,
    p. 28, supporting the action of O(n) on O(n, m) in 2.7.16, p. 139.
    Supporting lemma. *)
Lemma orthogonal_injection_action_member (g : O) (f : OI) :
  orthogonal_injections (hom_comp (om g) (orthogonal_injection_map f) : HUV).
Proof.
move=> x y.
change (B (om g (orthogonal_injection_map f x)) (om g (orthogonal_injection_map f y)) = C x y).
rewrite (orthogonal_element_inner g).
exact: (orthogonal_injection_map_orthogonal f x y).
Qed.

(** Source for [orthogonal_injection_action]: the action
    A(g, f) = g o f of O(n) on O(n, m), Federer 2.7.16, p. 139.
    Definition. *)
Definition orthogonal_injection_action (g : O) (f : OI) : OI :=
  exist _ (hom_comp (om g) (orthogonal_injection_map f) : HUV)
    (mem_set (orthogonal_injection_action_member g f)).

(** Source for [orthogonal_injection_actionE]: A(g, f)(u) = g(f(u)),
    Federer 2.7.16, p. 139. Supporting lemma. *)
Lemma orthogonal_injection_actionE (g : O) (f : OI) u :
  orthogonal_injection_map (orthogonal_injection_action g f) u = om g (orthogonal_injection_map f u).
Proof. exact: hom_compE. Qed.

Variables (mulS : O -> O -> O) (invS : O -> O) (eS : O).
Hypothesis hS : is_subgroup_restriction (linear_group_mul hB hb) (linear_group_inv hB hb)
  (linear_group_unit hB hb) O mulS invS eS.

(** Source for [hOT]: O(n) is a topological group, Federer 2.7.16,
    p. 139, used in this section. *)
Let hOT : is_topological_group mulS invS eS := lch_group_topological (orthogonal_group_lch hS).
(** Source for [hOG]: the group laws of O(n), used in this section. *)
Let hOG : is_group_laws mulS invS eS := topological_group_laws hOT.
(** Source for [hOc]: O(n) is compact, Federer 2.7.16, p. 139, used in
    this section. *)
Let hOc : compact [set: O] := @orthogonal_group_compact_space R V B hB n b hb.

(** Source for [orthogonal_projection_action_member]: p o g^{-1} is an
    orthogonal projection for g in O(n) and p in O*(n, m): if p is the
    adjoint of the orthogonal injection h, then p o g^{-1} is the adjoint
    of g o h, Federer 1.7.4, p. 30, supporting the action of O(n) on
    O*(n, m) in 2.7.16, p. 139. Supporting lemma. *)
Lemma orthogonal_projection_action_member (g : O) (p : OP) :
  orthogonal_projections (hom_comp (orthogonal_projection_map p) (om (invS g)) : HVU).
Proof.
have [h [hh hadj]] := orthogonal_projection_map_projection p.
have [hgi hig] := orthogonal_element_inv hS g.
exists (linear_comp (hom_as_linear (om g)) h); split.
  by move=> x y; rewrite /linear_comp /= (orthogonal_element_inner g) hh.
move=> x y.
change (C x (orthogonal_projection_map p (om (invS g) y)) = B (om g (h x)) y).
rewrite hadj -{2}(hig y); exact: esym (orthogonal_element_inner g _ _).
Qed.

(** Source for [orthogonal_projection_action]: the action
    A(g, p) = p o g^{-1} of O(n) on O*(n, m), Federer 2.7.16, p. 139.
    Definition. *)
Definition orthogonal_projection_action (g : O) (p : OP) : OP :=
  exist _ (hom_comp (orthogonal_projection_map p) (om (invS g)) : HVU)
    (mem_set (orthogonal_projection_action_member g p)).

(** Source for [orthogonal_projection_actionE]: A(g, p)(v) =
    p(g^{-1}(v)), Federer 2.7.16, p. 139. Supporting lemma. *)
Lemma orthogonal_projection_actionE (g : O) (p : OP) v :
  orthogonal_projection_map (orthogonal_projection_action g p) v =
    orthogonal_projection_map p (om (invS g) v).
Proof. exact: hom_compE. Qed.

(** Source for [orthogonal_injections_hausdorff]: O(n, m) is a Hausdorff
    space, Federer 2.7.1, p. 121, and 2.7.16, p. 139. Supporting lemma. *)
Lemma orthogonal_injections_hausdorff : hausdorff_space OI.
Proof. exact: set_type_hausdorff (@hom_space_hausdorff R U V C B hC hB m c hc). Qed.

(** Source for [orthogonal_projections_hausdorff]: O*(n, m) is a
    Hausdorff space, Federer 2.7.1, p. 121, and 2.7.16, p. 139.
    Supporting lemma. *)
Lemma orthogonal_projections_hausdorff : hausdorff_space OP.
Proof. exact: set_type_hausdorff (@hom_space_hausdorff R V U B C hB hC n b hb). Qed.

(** Source for [orthogonal_injection_action_continuous]: the action of
    O(n) on O(n, m) is continuous, Federer 2.7.1, p. 121, and 2.7.16,
    pp. 134 and 139. Supporting lemma. *)
Lemma orthogonal_injection_action_continuous :
  continuous (fun p : O * OI => orthogonal_injection_action p.1 p.2).
Proof.
apply: set_type_continuous_into.
have -> : set_val \o (fun p : O * OI => orthogonal_injection_action p.1 p.2) =
    (fun q : HVV * HUV => (hom_comp (q.1 : Hom V V) (q.2 : Hom U V) : HUV)) \o
      (fun p : O * OI => ((om p.1 : HVV), (set_val p.2 : HUV))).
  by [].
have hp : continuous (fun p : O * OI => ((om p.1 : HVV), (set_val p.2 : HUV))).
  apply: (@topological_pair_continuous (O * OI)%type HVV HUV).
  - move=> q; exact: continuous_comp (@first_projection_continuous O OI q)
      (@orthogonal_element_continuous R V B hB n b hb q.1).
  - move=> q; exact: continuous_comp (@second_projection_continuous O OI q)
      (@set_type_val_continuous HUV orthogonal_injections q.2).
move=> p; apply: continuous_comp; first exact: hp.
exact: (@hom_composition_continuous_general R U V V C B B hC hB hB m c n b hc hb _).
Qed.

(** Source for [orthogonal_projection_action_continuous]: the action of
    O(n) on O*(n, m) is continuous, Federer 2.7.1, p. 121, and 2.7.16,
    pp. 134 and 139: composition and the inversion of O(n) are
    continuous. Supporting lemma. *)
Lemma orthogonal_projection_action_continuous :
  continuous (fun p : O * OP => orthogonal_projection_action p.1 p.2).
Proof.
apply: set_type_continuous_into.
have -> : set_val \o (fun p : O * OP => orthogonal_projection_action p.1 p.2) =
    (fun q : HVU * HVV => (hom_comp (q.1 : Hom V U) (q.2 : Hom V V) : HVU)) \o
      (fun p : O * OP => ((set_val p.2 : HVU), (om (invS p.1) : HVV))).
  by [].
have hp : continuous (fun p : O * OP => ((set_val p.2 : HVU), (om (invS p.1) : HVV))).
  apply: (@topological_pair_continuous (O * OP)%type HVU HVV).
  - move=> q; exact: continuous_comp (@second_projection_continuous O OP q)
      (@set_type_val_continuous HVU orthogonal_projections q.2).
  - move=> q.
    have h1 := @first_projection_continuous O OP q.
    have h2 : {for q.1, continuous invS} := @topological_group_inv_continuous _ _ _ _ hOT q.1.
    have h3 : {for invS q.1, continuous (fun g : O => (om g : HVV))}.
      exact: (@orthogonal_element_continuous R V B hB n b hb (invS q.1)).
    exact: (continuous_comp h1 (continuous_comp h2 h3)).
move=> p; apply: continuous_comp; first exact: hp.
exact: (@hom_composition_continuous_general R V V U B B C hB hB hC n b n b hb hb _).
Qed.

(** Source for [orthogonal_injection_action_compatible]: A(gh, f) =
    A(g, A(h, f)), Federer 2.7.1, p. 121, for the action of O(n) on
    O(n, m), 2.7.16, p. 139. Supporting lemma. *)
Lemma orthogonal_injection_action_compatible g h f :
  orthogonal_injection_action (mulS g h) f =
    orthogonal_injection_action g (orthogonal_injection_action h f).
Proof.
apply: orthogonal_injection_ext=> u.
by rewrite !orthogonal_injection_actionE (orthogonal_element_mulE hS).
Qed.

(** Source for [orthogonal_projection_action_compatible]: A(gh, p) =
    A(g, A(h, p)), Federer 2.7.1, p. 121, for the action of O(n) on
    O*(n, m), 2.7.16, p. 139: (gh)^{-1} = h^{-1} g^{-1}. Supporting
    lemma. *)
Lemma orthogonal_projection_action_compatible g h p :
  orthogonal_projection_action (mulS g h) p =
    orthogonal_projection_action g (orthogonal_projection_action h p).
Proof.
apply: orthogonal_projection_ext=> v.
by rewrite !orthogonal_projection_actionE (group_invM hOG) (orthogonal_element_mulE hS).
Qed.

(** Source for [orthogonal_injection_action_transitive]: O(n) acts
    transitively on O(n, m), Federer 2.7.16, p. 139. Supporting lemma;
    see orthogonal_injection_transitive. *)
Lemma orthogonal_injection_action_transitive (f1 f2 : OI) :
  exists g, orthogonal_injection_action g f1 = f2.
Proof.
have [g [hg hgf]] := orthogonal_injection_transitive hC hB hc hb
  (orthogonal_injection_map_orthogonal f1) (orthogonal_injection_map_orthogonal f2).
exists (orthogonal_element_of hB hb hg); apply: orthogonal_injection_ext=> u.
by rewrite orthogonal_injection_actionE orthogonal_element_ofE hgf.
Qed.

(** Source for [orthogonal_projection_action_transitive]: O(n) acts
    transitively on O*(n, m), Federer 2.7.16, p. 139. Proof supplied: if
    p_i is the adjoint of the orthogonal injection h_i and g o h_1 = h_2
    with g in O(n), then p_1 o g^{-1} = p_2 (1.7.4, p. 30). *)
Lemma orthogonal_projection_action_transitive (p1 p2 : OP) :
  exists g, orthogonal_projection_action g p1 = p2.
Proof.
have [h1 [hh1 hadj1]] := orthogonal_projection_map_projection p1.
have [h2 [hh2 hadj2]] := orthogonal_projection_map_projection p2.
have [g [hg hgh]] := orthogonal_injection_transitive hC hB hc hb hh1 hh2.
pose k := orthogonal_element_of hB hb hg.
have [hki hik] := orthogonal_element_inv hS k.
exists k; apply: orthogonal_projection_ext=> v.
rewrite orthogonal_projection_actionE; apply: (inner_vectors_ext hC)=> u.
change (C u (orthogonal_projection_map p1 (om (invS k) v)) =
  C u (orthogonal_projection_map p2 v)).
rewrite hadj1 hadj2 -hgh.
change (B (h1 u) (om (invS k) v) = B (om k (h1 u)) v).
rewrite -{2}(hik v); exact: esym (orthogonal_element_inner k _ _).
Qed.

(** Source for [orthogonal_injections_homogeneous]: O(n, m) is a
    homogeneous space of O(n) through A(g, f) = g o f, Federer 2.7.1,
    p. 121, as used in 2.7.16, p. 139. Supporting theorem, by
    compact_transitive_homogeneous. *)
Theorem orthogonal_injections_homogeneous : is_homogeneous_space mulS orthogonal_injection_action.
Proof.
apply: (compact_transitive_homogeneous hOT hOc orthogonal_injections_hausdorff
  orthogonal_injection_action_continuous orthogonal_injection_action_compatible).
exact: orthogonal_injection_action_transitive.
Qed.

(** Source for [orthogonal_projections_homogeneous]: O*(n, m) is a
    homogeneous space of O(n) through A(g, p) = p o g^{-1}, Federer
    2.7.1, p. 121, as used in 2.7.16, p. 139. Supporting theorem, by
    compact_transitive_homogeneous. *)
Theorem orthogonal_projections_homogeneous : is_homogeneous_space mulS orthogonal_projection_action.
Proof.
apply: (compact_transitive_homogeneous hOT hOc orthogonal_projections_hausdorff
  orthogonal_projection_action_continuous orthogonal_projection_action_compatible).
exact: orthogonal_projection_action_transitive.
Qed.

(** Source for [orthogonal_injections_compact]: O(n, m) is compact,
    Federer 2.7.16, p. 139, being the image of O(n). Supporting lemma. *)
Lemma orthogonal_injections_compact : compact [set: OI].
Proof. exact: compact_homogeneous_space_compact hOc orthogonal_injections_homogeneous. Qed.

(** Source for [orthogonal_projections_compact]: O*(n, m) is compact,
    Federer 2.7.16, p. 139, being the image of O(n). Supporting lemma. *)
Lemma orthogonal_projections_compact : compact [set: OP].
Proof. exact: compact_homogeneous_space_compact hOc orthogonal_projections_homogeneous. Qed.

(** Source for [orthogonal_injections_invariant_measure]: "the O(n)
    invariant measures theta_{n,m} over O(n, m)", Federer 2.7.16,
    p. 139: for a point f_0 of O(U, V) there is exactly one O(V)
    invariant measure over O(U, V) with total measure 1, and it equals
    (A^f)_# theta for every f in O(U, V) and the normalised Haar measure
    theta of O(V). Direct formalisation. *)
Theorem orthogonal_injections_invariant_measure (f0 : OI) :
  exists phi : set OI -> \bar R,
    [/\ is_normalised_invariant_measure orthogonal_injection_action phi,
      forall psi, is_normalised_invariant_measure orthogonal_injection_action psi -> psi = phi &
      forall theta f, is_normalised_haar_measure mulS theta ->
        measure_pushforward (orbit_map orthogonal_injection_action f) theta = phi].
Proof.
exact: (normalised_invariant_measure_exists R (orthogonal_group_lch hS) hOc
  orthogonal_injections_homogeneous orthogonal_injections_hausdorff f0).
Qed.

(** Source for [orthogonal_projections_invariant_measure]: "the O(n)
    invariant measures ... theta*_{n,m} over O*(n, m)", Federer 2.7.16,
    p. 139: for a point p_0 of O*(V, U) there is exactly one O(V)
    invariant measure over O*(V, U) with total measure 1, and it equals
    (A^p)_# theta for every p in O*(V, U) and the normalised Haar measure
    theta of O(V). Direct formalisation. *)
Theorem orthogonal_projections_invariant_measure (p0 : OP) :
  exists phi : set OP -> \bar R,
    [/\ is_normalised_invariant_measure orthogonal_projection_action phi,
      forall psi, is_normalised_invariant_measure orthogonal_projection_action psi -> psi = phi &
      forall theta p, is_normalised_haar_measure mulS theta ->
        measure_pushforward (orbit_map orthogonal_projection_action p) theta = phi].
Proof.
exact: (normalised_invariant_measure_exists R (orthogonal_group_lch hS) hOc
  orthogonal_projections_homogeneous orthogonal_projections_hausdorff p0).
Qed.

End InjectionSpaces.

Arguments orthogonal_injections {R U V C B} hC hB {m c} hc _.
Arguments orthogonal_projections {R U V C B} hC hB {n b} hb _.
Arguments orthogonal_injection_map {R U V C B hC hB m c hc} f.
Arguments orthogonal_projection_map {R U V C B hC hB n b hb} p.
Arguments orthogonal_injection_action {R U V C B} hC hB {m c n b} hc hb g f.
Arguments orthogonal_projection_action {R U V C B} hC hB {n b} hb {mulS invS eS} hS g p.
