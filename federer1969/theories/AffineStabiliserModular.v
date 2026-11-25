(** Federer (1969), 2.7.16, example (5), printed p. 138: "choosing an m
    dimensional vectorsubspace W of R^n we now find that the isotropy group
    G^W equals M^{-1}(H x W), where H = GL(n, R) cap {h : h(W) = W}, and
    argue as above to prove that the modular function of G^W has the value
    |det[L(g)|W]|^{-1} Delta_H[L(g)] at g." The absolute value bars are
    those of the erratum (book p. 138, line 34). Here G is the affine group
    of AffineGroupTopology.v, the pairs (g, z) standing for tau_z o g, W is
    a subspace of V with a base of m vectors, H is subspace_stabiliser of
    example (3), and M^{-1}(H x W) is the set affine_subspace_stabiliser of
    the pairs (h, z) with h in H and z in W, a closed subgroup of G. "Argue
    as above" is carried out as in AffineGroupModular.v, with W in place of
    R^n. The translations (1_V, z), z in W, form a closed normal abelian
    subgroup of G^W, so Delta_{G^W} = 1 on them. The group G^W acts on the
    space W, with the inner product of V restricted to W, by A((h, z), w) =
    z + h(w); W is a homogeneous space of G^W (2.7.1, p. 121), and every
    Haar integral of the additive group of W is |det[L(.)|W]|^{-1} covariant
    for this action (FiniteHaarLinear.v for the restriction h|W, and
    translation invariance). The isotropy group of 0 consists of the (h, 0)
    and is isomorphic to H, so Weil's condition 2.7.11(1), p. 128, gives
    Delta_{G^W}(h, 0) = |det(h|W)|^{-1} Delta_H(h); finally (h, z) = (1_V,
    z)(h, 0). *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealMetricBackground InnerProductUP InnerProductLaws InnerNorm InnerMetric
  InnerNormedTopology LinearBasis Bilinear TensorUP Hom HomInner FiniteDualDimension ModuleQuotient
  SubspaceCarrier GrassmannSubspaces InnerProductRestriction InvariantRestriction ExteriorDeterminant
  EuclideanLinearMaps CompactSupportFunctionUP DaniellIntegralUP HomeomorphismUP IsotropyGroupTopology
  TopologicalProductMaps TopologicalGroupUP TopologicalGroupLaws HomogeneousSpaceUP HomogeneousSpaceLaws
  GroupMultiplicationHomogeneous CovariantIntegralUP CovariantIntegralLaws HaarIntegralUP HaarIntegralExistence
  ModularFunctionUP ModularFunction NormalSubgroupUP WeilCondition HomSpaceTopology LinearGroupTopology
  LinearGroupSealed HomHaarCovariance FiniteHaarLinear AffineGroupTopology SubspaceStabiliser
  GroupIsomorphismModular AffineGroupModular.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section SubspaceTopology.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable Ws : subspace V.
Local Notation VT := (inner_metric_space hB).
Local Notation WT := (inner_metric_space (restricted_inner_productP hB Ws)).

(** Source for [subspace_val_norm]: the inclusion of W into V preserves
    the norm of the restricted inner product, Federer 1.7.1, p. 28;
    supporting "an m dimensional vectorsubspace W of R^n" as a
    topological subspace, 2.7.16, p. 138. Supporting lemma. *)
Lemma subspace_val_norm (w : WT) : `|(subspace_val w : VT)| = `|w|.
Proof.
rewrite !inner_norm_topologyE; symmetry; apply: inner_norm_value.
  exact: inner_norm_nonnegative.
by rewrite inner_norm_sqr.
Qed.

(** Source for [subspace_val_continuous]: the inclusion of W into V is
    continuous, Federer 2.7.16, p. 138. Supporting lemma. *)
Lemma subspace_val_continuous : continuous (fun w : WT => (subspace_val w : VT)).
Proof.
move=> w; apply/(@cvgrPdist_lt _ _ _ (nbhs w) (nbhs_filter w))=> eps heps.
apply: (filterS _ (nbhsx_ballx w _ heps))=> y; rewrite -ball_normE /= => hy.
have -> : (subspace_val w : VT) - subspace_val y = subspace_val (w - y) by rewrite linearB.
by rewrite subspace_val_norm.
Qed.

(** Source for [subspace_continuous_into]: a map into W is continuous
    when its composition with the inclusion into V is, Federer 2.7.16,
    p. 138. Supporting lemma. *)
Lemma subspace_continuous_into (T : topologicalType) (F : T -> WT) :
  continuous (fun t => (subspace_val (F t) : VT)) -> continuous F.
Proof.
move=> hF t; apply/(@cvgrPdist_lt _ _ _ (nbhs t) (nbhs_filter t))=> eps heps.
have := (proj1 (@cvgrPdist_lt _ VT _ (nbhs t) (nbhs_filter t) (fun s => (subspace_val (F s) : VT))
  (subspace_val (F t)))) (hF t) eps heps.
apply: filterS=> s hs.
by rewrite -subspace_val_norm linearB.
Qed.

End SubspaceTopology.

Section AffineStabiliser.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Variable Ws : subspace V.
Variable m : nat.
Hypothesis hW : grassmann_pred m Ws.
Local Notation HVV := (inner_metric_space (hom_inner_productP hB hB hb)).
Local Notation VT := (inner_metric_space hB).
Local Notation GL := (set_type (linear_group hB hb)).
Local Notation AG := (GL * VT)%type.
Local Notation mul := (linear_group_mul hB hb).
Local Notation inv := (linear_group_inv hB hb).
Local Notation unit := (linear_group_unit hB hb).
Local Notation hG := (linear_group_operations hB hb).
Local Notation amul := (affine_group_mul hB hb).
Local Notation ainv := (affine_group_inv hB hb).
Local Notation aunit := (affine_group_unit hB hb).
Local Notation Hs := (subspace_stabiliser hB hb Ws).
Local Notation Stab := (set_type Hs).
Local Notation hBW := (restricted_inner_productP hB Ws).
Local Notation WT := (inner_metric_space hBW).
Local Notation KW := (@compactly_supported_continuous_functions R WT).

(** Source for [hgl]: the group laws of GL(V), used in this section. *)
Let hgl := linear_group_group_laws hG.

(** Source for [subspace_set_closed]: an m dimensional subspace W is a
    closed subset of V, Federer 2.7.16, p. 138: with a base adapted to
    W, W is the common zero set of continuous linear functions.
    Supporting lemma. *)
Lemma subspace_set_closed : closed [set x : VT | Ws x].
Proof.
have [w hw] := hW.
have [e [heb hew]] := adapted_basis_exists hb hw.
have -> : [set x : VT | Ws x] =
    \bigcap_(j in [set: 'I_(n - m)]) [set x : VT | (dual_basis heb (rshift m j) x : R) = 0].
  apply/seteqP; split=> x.
  - by move=> hx j _; exact: ((adapted_subspaceE hw heb hew x).1 hx j).
  - by move=> hx; apply/(adapted_subspaceE hw heb hew x)=> j; exact: hx j I.
apply: closed_bigI=> j _.
have -> : [set x : VT | (dual_basis heb (rshift m j) x : R) = 0] =
    (fun x : VT => (dual_basis heb (rshift m j) x : R^o)) @^-1` [set 0] by [].
by apply: preimage_closed; [move=> x _; exact: (linear_functional_continuous hb)|exact: closed_eq].
Qed.

(** Source for [affine_subspace_stabiliser]: "the isotropy group G^W
    equals M^{-1}(H x W), where H = GL(n, R) cap {h : h(W) = W}",
    Federer 2.7.16, p. 138: the pairs (h, z) with h in H and z in W.
    Definition. *)
Definition affine_subspace_stabiliser : set AG := [set p | Hs p.1 /\ Ws p.2].

(** Source for [affine_subspace_stabiliser_subgroup]: M^{-1}(H x W) is
    a subgroup of G, Federer 2.7.16, p. 138. Supporting lemma. *)
Lemma affine_subspace_stabiliser_subgroup : is_subgroup amul ainv aunit affine_subspace_stabiliser.
Proof.
have hH := subspace_stabiliser_subgroup hB hb Ws.
split.
- by split; [exact: (subgroup_unit hH)|exact: subspace_zero].
- move=> p q [hp1 hp2] [hq1 hq2]; split; first exact: (subgroup_mul hH hp1 hq1).
  by apply: subspace_add=> //; exact: (subspace_stabiliser_invariant hp1).
- move=> p [hp1 hp2]; split; first exact: (subgroup_inv hH hp1).
  apply: subspace_opp; exact: (subspace_stabiliser_invariant (subgroup_inv hH hp1)).
Qed.

(** Source for [affine_subspace_stabiliser_closed]: M^{-1}(H x W) is
    closed in G, Federer 2.7.16, p. 138: H is closed (example (3)) and W
    is closed. Supporting lemma. *)
Lemma affine_subspace_stabiliser_closed : closed affine_subspace_stabiliser.
Proof.
have -> : affine_subspace_stabiliser = (@fst GL VT @^-1` Hs) `&` (@snd GL VT @^-1` [set x : VT | Ws x]) by [].
apply: closedI.
- by apply: preimage_closed; [move=> p _; exact: first_projection_continuous|exact: (subspace_stabiliser_closed hW)].
- by apply: preimage_closed; [move=> p _; exact: second_projection_continuous|exact: subspace_set_closed].
Qed.

(** Source for [affine_subspace_stabiliser_restriction_exists]: G^W is
    a group with the operations of G, Federer 2.7.16, p. 138. Existence
    of the restricted operations. *)
Theorem affine_subspace_stabiliser_restriction_exists :
  exists mulK invK eK, is_subgroup_restriction amul ainv aunit affine_subspace_stabiliser mulK invK eK.
Proof. exact: subgroup_restriction_exists affine_subspace_stabiliser_subgroup. Qed.

Local Notation KS := (set_type affine_subspace_stabiliser).

(** Source for [affine_stabiliser_linear]: L(g) in H for g in G^W,
    Federer 2.7.16, p. 138. Definition. *)
Definition affine_stabiliser_linear (k : KS) : Stab := exist _ (set_val k).1 (mem_set (set_valP k).1).

(** Source for [affine_stabiliser_linear_continuous]: g |-> L(g) is
    continuous from G^W to H, Federer 2.7.16, p. 138. Supporting
    lemma. *)
Lemma affine_stabiliser_linear_continuous : continuous affine_stabiliser_linear.
Proof.
apply: set_type_continuous_into=> k.
apply: (@continuous_comp KS AG GL set_val (@fst GL VT)); first exact: set_type_val_continuous.
exact: first_projection_continuous.
Qed.

(** Source for [affine_stabiliser_action_mem]: z + h(w) belongs to W for
    (h, z) in G^W and w in W, Federer 2.7.16, p. 138. Supporting
    lemma. *)
Lemma affine_stabiliser_action_mem (k : KS) (w : WT) :
  Ws ((set_val k).2 + (set_val (set_val k).1 : Hom V V) (subspace_val w)).
Proof.
have [h1 h2] := set_valP k.
by apply: subspace_add=> //; apply: (subspace_stabiliser_invariant h1); exact: subspace_valP.
Qed.

(** Source for [affine_stabiliser_action]: the action
    A((h, z), w) = z + h(w) of G^W on W, Federer 2.7.16, p. 138
    ("argue as above", the usual action of example (5) restricted to
    W). Definition. *)
Definition affine_stabiliser_action (k : KS) (w : WT) : WT := subspace_lift (affine_stabiliser_action_mem k w).

(** Source for [affine_stabiliser_actionE]: A((h, z), w) = z + h(w),
    Federer 2.7.16, p. 138. Supporting lemma. *)
Lemma affine_stabiliser_actionE (k : KS) (w : WT) :
  subspace_val (affine_stabiliser_action k w) = affine_group_action hB hb (set_val k) (subspace_val w).
Proof. by rewrite subspace_liftE. Qed.

Variables (mulK : KS -> KS -> KS) (invK : KS -> KS) (eK : KS).
Hypothesis hK : is_subgroup_restriction amul ainv aunit affine_subspace_stabiliser mulK invK eK.
Variables (mulS : Stab -> Stab -> Stab) (invS : Stab -> Stab) (eS : Stab).
Hypothesis hS : is_subgroup_restriction mul inv unit Hs mulS invS eS.

(** Source for [hKl]: G^W is a locally compact Hausdorff topological
    group, Federer 2.7.16, p. 138, used in this section. *)
Let hKl : is_locally_compact_hausdorff_group mulK invK eK :=
  subgroup_restriction_locally_compact_hausdorff hK (affine_group_lch hB hb) affine_subspace_stabiliser_closed.

(** Source for [hSl]: H is a locally compact Hausdorff topological
    group, Federer 2.7.16, p. 137, used in this section. *)
Let hSl : is_locally_compact_hausdorff_group mulS invS eS := subspace_stabiliser_lch hW hS.

(** Source for [affine_stabiliser_linear_mul]: L is a homomorphism of
    G^W into H, Federer 2.7.16, p. 138. Supporting lemma. *)
Lemma affine_stabiliser_linear_mul (k l : KS) :
  affine_stabiliser_linear (mulK k l) = mulS (affine_stabiliser_linear k) (affine_stabiliser_linear l).
Proof.
apply: val_inj; rewrite /= -!set_valE (subgroup_restriction_mul hS) (subgroup_restriction_mul hK) /=.
by [].
Qed.

(** Source for [affine_stabiliser_action_continuous]: the action of G^W
    on W is continuous, Federer 2.7.1, p. 121, for 2.7.16, p. 138.
    Supporting lemma. *)
Lemma affine_stabiliser_action_continuous :
  continuous (fun q : KS * WT => affine_stabiliser_action q.1 q.2).
Proof.
apply: subspace_continuous_into.
have hAc := homogeneous_action_continuous (affine_group_homogeneous hB hb).
have -> : (fun q : KS * WT => (subspace_val (affine_stabiliser_action q.1 q.2) : VT)) =
    (fun r : AG * VT => affine_group_action hB hb r.1 r.2) \o
      (fun q : KS * WT => (set_val q.1, (subspace_val q.2 : VT))).
  by apply: funext=> q; exact: affine_stabiliser_actionE.
move=> q; apply: continuous_comp; last exact: hAc.
apply: (@topological_pair_continuous (KS * WT)%type AG VT).
- move=> r; apply: (@continuous_comp (KS * WT)%type KS AG (@fst KS WT) set_val r).
    exact: first_projection_continuous.
  exact: set_type_val_continuous.
- move=> r; apply: (@continuous_comp (KS * WT)%type WT VT (@snd KS WT) (fun w : WT => (subspace_val w : VT)) r).
    exact: second_projection_continuous.
  exact: subspace_val_continuous.
Qed.

(** Source for [affine_stabiliser_action_compatible]: A(gh, w) =
    A(g, A(h, w)), Federer 2.7.1, p. 121. Supporting lemma. *)
Lemma affine_stabiliser_action_compatible (k l : KS) (w : WT) :
  affine_stabiliser_action (mulK k l) w = affine_stabiliser_action k (affine_stabiliser_action l w).
Proof.
apply: subspace_val_injective; rewrite !affine_stabiliser_actionE (subgroup_restriction_mul hK).
by rewrite /affine_group_action affine_group_map_mul.
Qed.

(** Source for [affine_stabiliser_translate_mem]: (h, z + y - y_0) lies
    in G^W for (h, z) in G^W and y, y_0 in W, Federer 2.7.16, p. 138.
    Supporting lemma. *)
Lemma affine_stabiliser_translate_mem (k : KS) (y y0 : WT) :
  affine_subspace_stabiliser ((set_val k).1, (set_val k).2 + (subspace_val y - subspace_val y0)).
Proof.
have [h1 h2] := set_valP k; split=> //.
by apply: subspace_add=> //; apply: subspace_sub; exact: subspace_valP.
Qed.

(** Source for [affine_stabiliser_orbit_open]: the orbit maps of the
    action of G^W on W are open, Federer 2.7.1, p. 121. Supporting
    lemma: for (h, z) in an open set U of G^W and y_0 = z + h(w), the
    continuous map y |-> (h, z + y - y_0) carries y_0 to (h, z), and
    (h, z + y - y_0) maps w to y. *)
Lemma affine_stabiliser_orbit_open (w : WT) : is_open_map (orbit_map affine_stabiliser_action w).
Proof.
move=> Uo hUo; rewrite openE=> y0 [k hk <-]; rewrite /interior.
pose y1 := affine_stabiliser_action k w.
pose zeta := fun y : WT => (exist _ ((set_val k).1, (set_val k).2 + (subspace_val y - subspace_val y1))
  (mem_set (affine_stabiliser_translate_mem k y y1)) : KS).
have hc2 : continuous (fun y : WT => ((set_val k).2 + (subspace_val y - subspace_val y1) : VT)).
  have -> : (fun y : WT => ((set_val k).2 + (subspace_val y - subspace_val y1) : VT)) =
      (fun _ : WT => ((set_val k).2 : VT)) + ((fun y : WT => (subspace_val y : VT)) - (fun _ => (subspace_val y1 : VT))).
    by apply: funext.
  move=> x; apply: continuousD; first exact: cst_continuous.
  apply: continuousB; last exact: cst_continuous.
  exact: subspace_val_continuous.
have hz : continuous zeta.
  apply: set_type_continuous_into=> y.
  apply: (@topological_pair_continuous WT GL VT (fun _ => (set_val k).1)
    (fun y : WT => ((set_val k).2 + (subspace_val y - subspace_val y1) : VT))); last exact: hc2.
  exact: cst_continuous.
have hz1 : zeta y1 = k.
  apply: val_inj; rewrite /= -set_valE subrr addr0.
  by case: (set_val k).
have hzA y : affine_stabiliser_action (zeta y) w = y.
  apply: subspace_val_injective; rewrite affine_stabiliser_actionE /affine_group_action /affine_group_map.
  change ((set_val k).2 + (subspace_val y - subspace_val y1) +
    (set_val (set_val k).1 : Hom V V) (subspace_val w) = subspace_val y).
  rewrite /y1 affine_stabiliser_actionE /affine_group_action /affine_group_map.
  rewrite opprD !addrA subrK (addrC (set_val k).2).
  exact: addrK.
have hpre : open (zeta @^-1` Uo) by apply: open_comp hUo=> y _; exact: hz.
have hy1 : (zeta @^-1` Uo) y1 by rewrite /= hz1.
apply: (@filterS _ _ (nbhs_filter _) _ _ _ (open_nbhs_nbhs (conj hpre hy1))).
by move=> y hy; exists (zeta y)=> //; exact: hzA.
Qed.

(** Source for [affine_stabiliser_unit_translation_mem]: (1_V, y - w)
    lies in G^W for w, y in W, Federer 2.7.16, p. 138. Supporting
    lemma. *)
Lemma affine_stabiliser_unit_translation_mem (y w : WT) :
  affine_subspace_stabiliser (unit, subspace_val y - subspace_val w).
Proof.
split; first exact: (subgroup_unit (subspace_stabiliser_subgroup hB hb Ws)).
by apply: subspace_sub; exact: subspace_valP.
Qed.

(** Source for [affine_stabiliser_homogeneous]: W is a homogeneous space
    of G^W through A((h, z), w) = z + h(w), Federer 2.7.1, p. 121, as
    used in "argue as above", 2.7.16, p. 138. Supporting theorem. *)
Theorem affine_stabiliser_homogeneous : is_homogeneous_space mulK affine_stabiliser_action.
Proof.
split.
- exact: affine_stabiliser_action_continuous.
- exact: affine_stabiliser_action_compatible.
- exact: affine_stabiliser_orbit_open.
- move=> w; apply/seteqP; split=> // y _.
  exists (exist _ (unit, subspace_val y - subspace_val w) (mem_set (affine_stabiliser_unit_translation_mem y w)))=> //.
  apply: subspace_val_injective; rewrite affine_stabiliser_actionE /= /affine_group_action /affine_group_map /=.
  by rewrite (linear_group_unitE hG) hom_identityE subrK.
Qed.

(** Source for [affine_stabiliser_space_hausdorff]: W is Hausdorff,
    Federer 2.7.1, p. 121. Supporting lemma. *)
Lemma affine_stabiliser_space_hausdorff : hausdorff_space WT.
Proof. exact: (@inner_space_hausdorff R (subspace_space Ws) _ hBW). Qed.

(** Source for [affine_stabiliser_character]: the function
    |det[L(.)|W]|^{-1} on G^W, Federer 2.7.16, p. 138 (with the bars of
    the erratum, p. 138, line 34). Definition. *)
Definition affine_stabiliser_character (k : KS) : R :=
  `|stabiliser_restriction_det hW (affine_stabiliser_linear k)|^-1.

(** Source for [affine_stabiliser_character_mul]: |det[L(.)|W]|^{-1} is
    a homomorphism, Federer 1.3.4, p. 16. Supporting lemma. *)
Lemma affine_stabiliser_character_mul (k l : KS) :
  affine_stabiliser_character (mulK k l) = affine_stabiliser_character k * affine_stabiliser_character l.
Proof.
rewrite /affine_stabiliser_character affine_stabiliser_linear_mul (stabiliser_restriction_det_mul hW hS).
by rewrite normrM invfM.
Qed.

(** Source for [affine_stabiliser_character_nonzero]: |det[L(.)|W]|^{-1}
    does not vanish, Federer 1.3.4, p. 16. Supporting lemma. *)
Lemma affine_stabiliser_character_nonzero (k : KS) : affine_stabiliser_character k != 0.
Proof.
by rewrite /affine_stabiliser_character invr_eq0 normr_eq0 stabiliser_restriction_det_nonzero.
Qed.

(** Source for [affine_stabiliser_character_continuous]:
    |det[L(.)|W]|^{-1} is continuous on G^W, Federer 2.7.16, p. 138.
    Supporting lemma. *)
Lemma affine_stabiliser_character_continuous :
  continuous (affine_stabiliser_character : KS -> real_line_metric R).
Proof.
have hd := @continuous_inverse_power R Stab (fun g : Stab => (stabiliser_restriction_det hW g : R^o)) 1
  (@stabiliser_restriction_det_continuous R V B hB n b hb Ws m hW)
  (@stabiliser_restriction_det_nonzero R V B hB n b hb Ws m hW).
have -> : (affine_stabiliser_character : KS -> real_line_metric R) =
    (fun g : Stab => (`|stabiliser_restriction_det hW g| ^- 1 : R^o)) \o affine_stabiliser_linear.
  by apply: funext=> k; rewrite /affine_stabiliser_character /= expr1.
move=> k; apply: continuous_comp; first exact: affine_stabiliser_linear_continuous.
exact: hd.
Qed.

(** Source for [affine_stabiliser_haar_covariant]: every Haar integral
    of the additive group of W is |det[L(.)|W]|^{-1} covariant for the
    action of G^W on W, Federer 2.7.16, p. 138, "argue as above" (the
    covariance of L^n in example (5) with W in place of R^n):
    u o A_{(h, z)} = (u o tau_z) o h|W, and
    mu(v o h|W) = |det(h|W)|^{-1} mu(v) (finite_haar_integral_linear).
    Supporting theorem. *)
Theorem affine_stabiliser_haar_covariant (mu : (WT -> R) -> R) :
  is_left_haar_integral (fun x y : WT => x + y) mu ->
  is_covariant_integral affine_stabiliser_action affine_stabiliser_character mu.
Proof.
move=> hmu.
have [w hw] := hW.
have hT := lch_group_topological (inner_additive_lch_group hBW hw).
have hLh := left_multiplication_homogeneous hT.
have hlaw := covariant_integral_law (nonzero_invariant_integral_invariant hmu).
split; first exact: (covariant_integral_daniell (nonzero_invariant_integral_invariant hmu)).
move=> u k hu.
pose z : WT := subspace_lift (set_valP k).2.
have hut : KW (u \o left_multiplication_action (fun x y : WT => x + y) z).
  exact: (compactly_supported_translate (topological_group_laws hT) hLh _ hu).
pose T := stabiliser_restriction (affine_stabiliser_linear k).
have e1 : u \o affine_stabiliser_action k = (u \o left_multiplication_action (fun x y : WT => x + y) z) \o
    (T : WT -> WT).
  apply: funext=> y; rewrite /= /left_multiplication_action; congr u.
  apply: subspace_val_injective; rewrite affine_stabiliser_actionE linearD.
  by [].
have hdet : det (euclidean_two_nonzero R) hw T = stabiliser_restriction_det hW (affine_stabiliser_linear k).
  exact: esym (stabiliser_restriction_detE hW hw _).
have hdet0 : det (euclidean_two_nonzero R) hw T != 0.
  by rewrite hdet; exact: stabiliser_restriction_det_nonzero.
rewrite e1 (@finite_haar_integral_linear R (subspace_space Ws) _ hBW m w hw mu T hmu hdet0 _ hut).
by rewrite (hlaw u z hu) mul1r hdet.
Qed.

(** Source for [affine_stabiliser_haar_nonzero_covariant]: a nonzero
    |det[L(.)|W]|^{-1} covariant integral on K(W) exists, Federer
    2.7.16, p. 138, with 2.7.5, p. 125. Supporting lemma. *)
Lemma affine_stabiliser_haar_nonzero_covariant :
  exists mu : (WT -> R) -> R,
    is_covariant_integral affine_stabiliser_action affine_stabiliser_character mu /\ exists2 v, KW v & mu v <> 0.
Proof.
have [w hw] := hW.
have [mu hmu] := left_haar_integral_exists R (inner_additive_lch_group hBW hw).
exists mu; split; first exact: affine_stabiliser_haar_covariant.
exact: (nonzero_invariant_integral_nonzero hmu).
Qed.

Local Notation K0 := (isotropy_subgroup affine_stabiliser_action (0 : WT)).

(** Source for [affine_stabiliser_linear_pair_mem]: (h, 0) lies in G^W
    for h in H, Federer 2.7.16, p. 138. Supporting lemma. *)
Lemma affine_stabiliser_linear_pair_mem (h : Stab) : affine_subspace_stabiliser (set_val h, 0).
Proof. by split; [exact: set_valP h|exact: subspace_zero]. Qed.

(** Source for [affine_stabiliser_linear_pair]: the member (h, 0) of
    G^W, Federer 2.7.16, p. 138. Definition. *)
Definition affine_stabiliser_linear_pair (h : Stab) : KS :=
  exist _ (set_val h, 0) (mem_set (affine_stabiliser_linear_pair_mem h)).

(** Source for [affine_stabiliser_isotropy_mem]: (h, 0) fixes 0, Federer
    2.7.16, p. 138: the isotropy group of 0 for the action of G^W on W
    is H. Supporting lemma. *)
Lemma affine_stabiliser_isotropy_mem (h : Stab) : K0 (affine_stabiliser_linear_pair h).
Proof.
rewrite /isotropy_subgroup /=; apply: subspace_val_injective.
rewrite affine_stabiliser_actionE /affine_group_action /affine_group_map.
change (0 + (set_val (set_val h) : Hom V V) (subspace_val (0 : WT)) = subspace_val (0 : WT)).
by rewrite linear0 add0r linear0.
Qed.

(** Source for [affine_stabiliser_isotropy_of]: H as the isotropy group
    of 0, h |-> (h, 0), Federer 2.7.16, p. 138. Definition. *)
Definition affine_stabiliser_isotropy_of (h : Stab) : K0 :=
  exist _ (affine_stabiliser_linear_pair h) (mem_set (affine_stabiliser_isotropy_mem h)).

(** Source for [affine_stabiliser_isotropy_translation]: members of the
    isotropy group of 0 have translation part 0, Federer 2.7.16,
    p. 138. Supporting lemma. *)
Lemma affine_stabiliser_isotropy_translation (t : K0) : (set_val (set_val t)).2 = 0.
Proof.
have h := set_valP t; rewrite /isotropy_subgroup /= in h.
have e := congr1 subspace_val h.
rewrite affine_stabiliser_actionE /affine_group_action /affine_group_map in e.
by rewrite !linear0 addr0 in e.
Qed.

(** Source for [affine_stabiliser_isotropy_homeomorphism]: h |-> (h, 0)
    is a homeomorphism of H onto the isotropy group of 0, Federer
    2.7.16, p. 138. Supporting lemma. *)
Lemma affine_stabiliser_isotropy_homeomorphism :
  is_homeomorphism_with_inverse affine_stabiliser_isotropy_of (fun t : K0 => affine_stabiliser_linear (set_val t)).
Proof.
split.
- apply: set_type_continuous_into; apply: set_type_continuous_into=> h.
  apply: (@topological_pair_continuous Stab GL VT (fun h : Stab => set_val h) (fun _ => (0 : VT))).
    exact: set_type_val_continuous.
  exact: cst_continuous.
- move=> t; apply: (@continuous_comp K0 KS Stab set_val affine_stabiliser_linear).
    exact: set_type_val_continuous.
  exact: affine_stabiliser_linear_continuous.
- by move=> h; apply: val_inj.
- move=> t; apply: val_inj; apply: val_inj; rewrite /= -!set_valE.
  have h0 := affine_stabiliser_isotropy_translation t.
  have -> : set_val (affine_stabiliser_linear (set_val t)) = (set_val (set_val t)).1 by [].
  by rewrite -h0 -surjective_pairing.
Qed.

Section IsotropyRestriction.
Variables (mul0 : K0 -> K0 -> K0) (inv0 : K0 -> K0) (e0 : K0).
Hypothesis h0 : is_subgroup_restriction mulK invK eK K0 mul0 inv0 e0.

(** Source for [affine_stabiliser_isotropy_of_mul]: h |-> (h, 0) is a
    homomorphism, Federer 2.7.16, p. 138. Supporting lemma. *)
Lemma affine_stabiliser_isotropy_of_mul (h h' : Stab) :
  affine_stabiliser_isotropy_of (mulS h h') = mul0 (affine_stabiliser_isotropy_of h) (affine_stabiliser_isotropy_of h').
Proof.
apply: val_inj; apply: val_inj; rewrite /= -!set_valE (subgroup_restriction_mul h0) (subgroup_restriction_mul hK) /=.
rewrite (subgroup_restriction_mul hS) /affine_group_mul /=.
by rewrite (linear0 (hom_as_linear (set_val (set_val h) : Hom V V))) addr0.
Qed.

(** Source for [affine_stabiliser_isotropy_modular]: the modular
    function of the isotropy group of 0 corresponds to Delta_H, Federer
    2.7.16, p. 138, the isotropy group being isomorphic to H. Supporting
    lemma. *)
Lemma affine_stabiliser_isotropy_modular (D0 : K0 -> R) (DH : Stab -> R) :
  is_modular_function mul0 inv0 D0 -> is_modular_function mulS invS DH ->
  forall t, D0 t = DH (affine_stabiliser_linear (set_val t)).
Proof.
move=> hD0 hDH t.
have hl0 : is_locally_compact_hausdorff_group mul0 inv0 e0.
  apply: (subgroup_restriction_locally_compact_hausdorff h0 hKl).
  exact: (isotropy_subgroup_closed affine_stabiliser_homogeneous affine_stabiliser_space_hausdorff).
have hiso := isomorphism_modular_function hSl hl0 affine_stabiliser_isotropy_homeomorphism
  affine_stabiliser_isotropy_of_mul hDH hD0.
by rewrite hiso (homeomorphism_right_inverse affine_stabiliser_isotropy_homeomorphism).
Qed.

End IsotropyRestriction.

(** Source for [affine_stabiliser_modular_linear_part]: "argue as above
    to prove that the modular function of G^W has the value
    |det[L(g)|W]|^{-1} Delta_H[L(g)] at g", Federer 2.7.16, p. 138, for
    g = (h, 0): by Weil's condition 2.7.11(1), p. 128, for the action of
    G^W on W, whose isotropy group at 0 is isomorphic to H. Supporting
    theorem. *)
Theorem affine_stabiliser_modular_linear_part (DK : KS -> R) (DH : Stab -> R) :
  is_modular_function mulK invK DK -> is_modular_function mulS invS DH ->
  forall h : Stab, DK (affine_stabiliser_linear_pair h) =
    `|stabiliser_restriction_det hW h|^-1 * DH h.
Proof.
move=> hDK hDH h.
have [mul0 [inv0 [e0 [h0 hl0]]]] := isotropy_group_exists (0 : WT) hKl affine_stabiliser_homogeneous
  affine_stabiliser_space_hausdorff.
have [D0 hD0] := modular_function_exists R hl0.
have [mu [hmu hmu0]] := affine_stabiliser_haar_nonzero_covariant.
have hWc := weil_condition_necessary hKl affine_stabiliser_homogeneous affine_stabiliser_space_hausdorff h0 hDK hD0
  affine_stabiliser_character_mul affine_stabiliser_character_nonzero affine_stabiliser_character_continuous hmu hmu0.
have := hWc (affine_stabiliser_isotropy_of h).
rewrite (affine_stabiliser_isotropy_modular h0 hD0 hDH) /= /affine_stabiliser_character.
have -> : affine_stabiliser_linear (affine_stabiliser_linear_pair h) = h by apply: val_inj.
by move=> <-.
Qed.

(** Source for [affine_stabiliser_translations]: "ker L|G^W", the pairs
    (1_V, z) with z in W, Federer 2.7.16, p. 138. Definition. *)
Definition affine_stabiliser_translations : set KS := [set k | (set_val k).1 = unit].

(** Source for [affine_stabiliser_translations_normal]: ker L|G^W is a
    normal subgroup of G^W, Federer 2.7.16, p. 138. Supporting lemma. *)
Lemma affine_stabiliser_translations_normal : is_normal_subgroup mulK invK eK affine_stabiliser_translations.
Proof.
rewrite /affine_stabiliser_translations.
split; first split.
- by rewrite /= (subgroup_restriction_unit hK).
- move=> k l hk hl; rewrite /= (subgroup_restriction_mul hK) /= in hk hl *.
  by rewrite hk hl (group_mul1g hgl).
- move=> k hk; rewrite /= (subgroup_restriction_inv hK) /= in hk *.
  by rewrite hk (group_inv1 hgl).
- move=> k s hs; rewrite /= !(subgroup_restriction_mul hK) (subgroup_restriction_inv hK) /= in hs *.
  by rewrite hs (group_mulg1 hgl) (group_mulgV hgl).
Qed.

(** Source for [affine_stabiliser_translations_closed]: ker L|G^W is
    closed, Federer 2.7.16, p. 138. Supporting lemma. *)
Lemma affine_stabiliser_translations_closed : closed affine_stabiliser_translations.
Proof.
have hH := lch_group_hausdorff (linear_group_operations_lch hB hb).
have hx : closed [set unit] by exact: accessible_closed_set1 (hausdorff_accessible hH) unit.
have -> : affine_stabiliser_translations = (fun k : KS => (set_val k).1) @^-1` [set unit] by [].
apply: preimage_closed hx=> k _.
apply: (@continuous_comp KS AG GL set_val (@fst GL VT)); first exact: set_type_val_continuous.
exact: first_projection_continuous.
Qed.

(** Source for [affine_stabiliser_modular_translations]: "ker L|G^W is
    abelian, hence Delta_{G^W}|ker L = 1", Federer 2.7.16, p. 138
    ("argue as above"). Supporting theorem. *)
Theorem affine_stabiliser_modular_translations (DK : KS -> R) :
  is_modular_function mulK invK DK -> forall k, affine_stabiliser_translations k -> DK k = 1.
Proof.
move=> hDK.
apply: (abelian_normal_modular_unit hKl affine_stabiliser_translations_normal
  affine_stabiliser_translations_closed)=> // k l hk hl.
apply: val_inj; rewrite /= -!set_valE !(subgroup_restriction_mul hK).
exact: affine_group_translations_commute.
Qed.

(** Source for [affine_stabiliser_translation_part_mem]: (1_V, z) lies in
    G^W for (h, z) in G^W, Federer 2.7.16, p. 138. Supporting lemma. *)
Lemma affine_stabiliser_translation_part_mem (k : KS) : affine_subspace_stabiliser (unit, (set_val k).2).
Proof. by split; [exact: (subgroup_unit (subspace_stabiliser_subgroup hB hb Ws))|exact: (set_valP k).2]. Qed.

(** Source for [affine_subspace_stabiliser_modular]: "the modular
    function of G^W has the value |det[L(g)|W]|^{-1} Delta_H[L(g)] at
    g", Federer 2.7.16, p. 138, with the absolute value of the erratum
    (book p. 138, line 34), for any modular functions Delta_{G^W} and
    Delta_H. Direct formalisation: g = (1_V, z)(h, 0). *)
Theorem affine_subspace_stabiliser_modular (DK : KS -> R) (DH : Stab -> R) :
  is_modular_function mulK invK DK -> is_modular_function mulS invS DH ->
  forall k : KS, DK k = `|stabiliser_restriction_det hW (affine_stabiliser_linear k)|^-1 *
    DH (affine_stabiliser_linear k).
Proof.
move=> hDK hDH k.
have [hM _] := modular_function_homomorphism hKl hDK.
pose tk : KS := exist _ (unit, (set_val k).2) (mem_set (affine_stabiliser_translation_part_mem k)).
have he : k = mulK tk (affine_stabiliser_linear_pair (affine_stabiliser_linear k)).
  apply: val_inj; rewrite /= -!set_valE (subgroup_restriction_mul hK) /= /affine_group_mul /=.
  rewrite (group_mul1g hgl) (linear_group_unitE hG) hom_identityE addr0.
  exact: surjective_pairing.
rewrite [in LHS]he hM (affine_stabiliser_modular_translations hDK) // mul1r.
exact: (affine_stabiliser_modular_linear_part hDK hDH).
Qed.

End AffineStabiliser.

Arguments affine_subspace_stabiliser {R V B} hB {n b} hb Ws p.
Arguments affine_stabiliser_linear {R V B hB n b hb Ws} k.
Arguments affine_stabiliser_linear_pair {R V B hB n b hb Ws} h.
