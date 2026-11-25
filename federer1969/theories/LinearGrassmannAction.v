(** Federer (1969), 2.7.16, example (4), printed p. 138: "For 0 < m < n, the
    action of GL(n, R) on G(n, m) (see 1.6.2) ... In fact, if W in G(n, m)
    and V = R^n, the isotropy group GL(n, R)^W is the group studied in (3)".
    Federer uses, without proof, that G(n, m) is a homogeneous space of
    GL(n, R) through A(g, W) = g[W] in the sense of 2.7.1, p. 121. Here V is
    a space with an inner product and a finite basis, G(V, m) carries the
    topology of GrassmannHomogeneousSpace.v (the initial topology of W |->
    P_W, P_W the orthogonal projection onto W, 1.7.4, p. 30), and GL(V) is
    the linear group of LinearGroupTopology.v with the sealed operations of
    LinearGroupSealed.v. For g in GL(V) the map Q = g o P_W o g^{-1} maps V
    into g[W] and fixes g[W], but is not orthogonal unless g is. The
    continuity of the action rests on the estimate ||P_{M'} - P_M|| <= 2 ||Q
    - Q_0|| whenever Q maps V into M' and fixes M', and Q_0 maps V into M
    and fixes M (grassmann_projection_difference_bound): with u = P_M(x) and
    y = x - P_M(x) one has u - P_{M'}(u) = z - P_{M'}(z) for z = (Q_0 -
    Q)(u), and |P_{M'}(y)|^2 = (Q - Q_0)(P_{M'}(y)) . y. Since (g, W) |-> g
    o P_W o g^{-1} is continuous (2.7.16, p. 134), so is (g, W) |->
    P_{g[W]}. The orbit maps are open because those of the subgroup O(V) are
    (example (6)), and O(V) acts transitively. The isotropy group of W is
    the group subspace_stabiliser of example (3). The local erratum has no
    entry for this passage of p. 138. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerProductLaws Bilinear InnerNorm InnerNormInequalities InnerMetric
  LinearBasis TensorUP Hom HomInner ModuleQuotient GrassmannSubspaces IsotropyGroupTopology
  TopologicalProductMaps TopologicalGroupUP TopologicalGroupLaws HomeomorphismUP HomogeneousSpaceUP
  HomogeneousSpaceLaws HomSpaceTopology LinearGroupTopology LinearGroupSealed OrthogonalGroupTopology
  OrthogonalGroupHaarMeasure GrassmannHomogeneousSpace SubspaceStabiliser SubgroupOrbitOpen.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ProjectionEstimate.
Variable R : realType.
Variables U V : lmodType R.
Variables (C : U -> U -> R) (B : V -> V -> R).
Hypotheses (hC : is_inner_product C) (hB : is_inner_product B).
Variables (m : nat) (c : 'I_m -> U) (n : nat) (b : 'I_n -> V).
Hypotheses (hc : is_basis c) (hb : is_basis b).
Local Notation P W := (grassmann_projection hC hB hc W).
Local Notation N := (inner_norm hB).
Local Notation onorm := (hom_operator_norm hB hB hb).

(** Source for [grassmann_projection_orthogonal]: P_W(x) . (x - P_W(x))
    = 0, Federer 1.7.4, p. 30, supporting 2.7.16, p. 138. Supporting
    lemma. *)
Lemma grassmann_projection_orthogonal (W : G V m) x : B (P W x) (x - P W x) = 0.
Proof.
have [h1 h2] := grassmann_projectionP hC hB hc W.
by rewrite (inner_symmetric hB); exact: h2 (h1 x).
Qed.

(** Source for [grassmann_projection_pythagoras]: |x|^2 = |P_W(x)|^2 +
    |x - P_W(x)|^2, Federer 1.7.1, p. 28, and 1.7.4, p. 30. Supporting
    lemma. *)
Lemma grassmann_projection_pythagoras (W : G V m) x : N x ^+ 2 = N (P W x) ^+ 2 + N (x - P W x) ^+ 2.
Proof.
rewrite !inner_norm_sqr.
have -> : B x x = B (P W x + (x - P W x)) (P W x + (x - P W x)) by rewrite addrC subrK.
by rewrite (inner_sum_square hB (P W x)) grassmann_projection_orthogonal !addr0.
Qed.

(** Source for [grassmann_projection_norm_le]: |P_W(x)| <= |x|, Federer
    1.7.4, p. 30. Supporting lemma. *)
Lemma grassmann_projection_norm_le (W : G V m) x : N (P W x) <= N x.
Proof.
rewrite -(@ler_pXn2r _ 2) ?nnegrE ?inner_norm_nonnegative //.
by rewrite (grassmann_projection_pythagoras W x) lerDl exprn_ge0 // inner_norm_nonnegative.
Qed.

(** Source for [grassmann_projection_residual_norm_le]: |x - P_W(x)| <=
    |x|, Federer 1.7.4, p. 30. Supporting lemma. *)
Lemma grassmann_projection_residual_norm_le (W : G V m) x : N (x - P W x) <= N x.
Proof.
rewrite -(@ler_pXn2r _ 2) ?nnegrE ?inner_norm_nonnegative //.
by rewrite (grassmann_projection_pythagoras W x) lerDr exprn_ge0 // inner_norm_nonnegative.
Qed.

(** Source for [grassmann_projection_difference_bound]: if Q maps V
    into M' and fixes M', and Q_0 maps V into M and fixes M, then
    ||P_{M'} - P_M|| <= 2 ||Q - Q_0||, Federer 1.7.4, p. 30, and 1.7.6,
    p. 33; supporting the continuity of the action of GL(n, R) on
    G(n, m) used in 2.7.16, p. 138. Supporting lemma: for x in V, with
    u = P_M(x) and y = x - P_M(x),
    (P_{M'} - P_M)(x) = P_{M'}(y) - (u - P_{M'}(u)),
    u - P_{M'}(u) = z - P_{M'}(z) for z = (Q_0 - Q)(u), and
    |P_{M'}(y)|^2 = (Q - Q_0)(P_{M'}(y)) . y. *)
Lemma grassmann_projection_difference_bound (M M' : G V m) (Q Q0 : Hom V V) :
  (forall x, grassmann_val M' (Q x)) -> (forall y, grassmann_val M' y -> Q y = y) ->
  (forall x, grassmann_val M (Q0 x)) -> (forall y, grassmann_val M y -> Q0 y = y) ->
  onorm (P M' - P M) <= (1 + 1) * onorm (Q - Q0).
Proof.
move=> hQ hQf hQ0 hQ0f.
have [hP1 hP2] := grassmann_projectionP hC hB hc M.
have [hP1' hP2'] := grassmann_projectionP hC hB hc M'.
pose d := onorm (Q - Q0).
have hd : 0 <= d := hom_operator_norm_nonnegative hB hB hb _.
apply: hom_operator_norm_least; first by rewrite mulr_ge0 // addr_ge0 ?ler01.
move=> x.
pose u := P M x; pose y := x - P M x.
have hlin (f : Hom V V) (a a' : V) : f (a - a') = f a - f a' := linearB (hom_as_linear f) a a'.
have hsplit : ((P M' - P M : Hom V V) x) = P M' y - (u - P M' u).
  have -> : ((P M' - P M : Hom V V) x) = P M' x - P M x by [].
  by rewrite /y /u hlin opprB addrA subrK.
have hux : N u <= N x := grassmann_projection_norm_le M x.
have hyx : N y <= N x := grassmann_projection_residual_norm_le M x.
have hQQ (a : V) : N ((Q - Q0 : Hom V V) a) <= d * N a := hom_operator_norm_bound hB hB hb _ a.
have hQQE (a : V) : ((Q - Q0 : Hom V V) a) = Q a - Q0 a by [].
(* the first term *)
have h1 : N (u - P M' u) <= d * N x.
  pose z := Q0 u - Q u.
  have hz : u - P M' u = z - P M' z.
    rewrite /z hlin (grassmann_projection_fixed hC hB hc (hQ u)).
    by rewrite (hQ0f u (hP1 x)) opprB addrA subrK.
  rewrite hz; apply: le_trans (grassmann_projection_residual_norm_le M' z) _.
  have -> : z = - ((Q - Q0 : Hom V V) u) by rewrite hQQE opprB.
  rewrite inner_normN; apply: le_trans (hQQ u) _.
  by rewrite ler_wpM2l.
(* the second term *)
have h2 : N (P M' y) <= d * N x.
  pose v := P M' y.
  have hyM w : grassmann_val M w -> B y w = 0 := hP2 x w.
  have hvv : N v ^+ 2 = B ((Q - Q0 : Hom V V) v) y.
    rewrite inner_norm_sqr.
    have e1 : B (y - v) v = 0 := hP2' y v (hP1' y).
    have e2 : B v v = B v y.
      apply/eqP; rewrite (inner_symmetric hB v y) eq_sym -subr_eq0.
      by rewrite -(bilBl (inner_bilinear hB)) e1.
    rewrite e2 hQQE (bilBl (inner_bilinear hB)) (hQf v (hP1' y)).
    by rewrite [B (Q0 v) y](inner_symmetric hB) (hyM _ (hQ0 v)) subr0.
  have hc' : N v ^+ 2 <= d * N v * N y.
    rewrite hvv; apply: le_trans (inner_cauchy_upper hB _ _) _.
    by rewrite ler_wpM2r ?inner_norm_nonnegative.
  have hvy : N v <= d * N y.
    have [hv0|hv0] := eqVneq (N v) 0.
      by rewrite hv0 mulr_ge0 ?inner_norm_nonnegative.
    have hvp : 0 < N v by rewrite lt_neqAle eq_sym hv0 inner_norm_nonnegative.
    by rewrite -(ler_pM2l hvp) -expr2 mulrA [N v * d]mulrC.
  apply: le_trans hvy _; exact: ler_wpM2l.
rewrite hsplit; apply: le_trans (inner_norm_triangle hB _ _) _.
rewrite inner_normN -mulrA mulrDl !mul1r.
exact: lerD.
Qed.

End ProjectionEstimate.

Section LinearAction.
Variable R : realType.
Variables U V : lmodType R.
Variables (C : U -> U -> R) (B : V -> V -> R).
Hypotheses (hC : is_inner_product C) (hB : is_inner_product B).
Variables (m : nat) (c : 'I_m -> U) (n : nat) (b : 'I_n -> V).
Hypotheses (hc : is_basis c) (hb : is_basis b).
Local Notation HVV := (inner_metric_space (hom_inner_productP hB hB hb)).
Local Notation GR := (grassmann_space hC hB hc hb).
Local Notation GL := (set_type (linear_group hB hb)).
Local Notation mul := (linear_group_mul hB hb).
Local Notation inv := (linear_group_inv hB hb).
Local Notation unit := (linear_group_unit hB hb).
Local Notation hG := (linear_group_operations hB hb).
Local Notation P W := (grassmann_projection hC hB hc W).
Local Notation onorm := (hom_operator_norm hB hB hb).
Local Notation O := (orthogonal_group hB hb).

(** Source for [linear_group_element_injective]: a member g of GL(V) is
    univalent, Federer 2.7.16, p. 134. Supporting lemma. *)
Lemma linear_group_element_injective (g : GL) : injective (hom_as_linear (set_val g : Hom V V)).
Proof. exact: (set_valP g). Qed.

(** Source for [linear_grassmann_action]: "the action of GL(n, R) on
    G(n, m)", Federer 2.7.16, p. 138: A(g, W) = g[W]. Definition. *)
Definition linear_grassmann_action (g : GL) (W : GR) : GR :=
  grassmann_image hC hB hc (@linear_group_element_injective g) W.

(** Source for [linear_grassmann_actionE]: y belongs to g[W] if and only
    if y = g(w) for some w in W, Federer 2.7.16, p. 138. Supporting
    lemma. *)
Lemma linear_grassmann_actionE (g : GL) (W : GR) y :
  grassmann_val (linear_grassmann_action g W : G V m) y <->
    exists2 w, grassmann_val (W : G V m) w & (set_val g : Hom V V) w = y.
Proof. by []. Qed.

(** Source for [linear_grassmann_conjugate]: the map g o P_W o g^{-1},
    Federer 2.7.16, p. 134, supporting the continuity of the action of
    GL(n, R) on G(n, m), p. 138. Definition. *)
Definition linear_grassmann_conjugate (g : GL) (W : GR) : Hom V V :=
  hom_comp (hom_comp (set_val g : Hom V V) (P W)) (set_val (inv g) : Hom V V).

(** Source for [linear_grassmann_conjugate_mem]: g o P_W o g^{-1} maps V
    into g[W], Federer 2.7.16, p. 138. Supporting lemma. *)
Lemma linear_grassmann_conjugate_mem (g : GL) (W : GR) x :
  grassmann_val (linear_grassmann_action g W : G V m) (linear_grassmann_conjugate g W x).
Proof.
rewrite /linear_grassmann_conjugate !hom_compE.
by exists (P W ((set_val (inv g) : Hom V V) x))=> //; exact: (grassmann_projectionP hC hB hc W).1.
Qed.

(** Source for [linear_grassmann_conjugate_fixed]: g o P_W o g^{-1}
    fixes g[W], Federer 1.7.4, p. 30, and 2.7.16, p. 138. Supporting
    lemma. *)
Lemma linear_grassmann_conjugate_fixed (g : GL) (W : GR) y :
  grassmann_val (linear_grassmann_action g W : G V m) y -> linear_grassmann_conjugate g W y = y.
Proof.
move=> [w hw <-]; rewrite /linear_grassmann_conjugate !hom_compE.
have [hgi _] := linear_group_inv_cancel hG g.
by rewrite hgi (grassmann_projection_fixed hC hB hc hw).
Qed.

(** Source for [linear_grassmann_conjugate_continuous]: (g, W) |->
    g o P_W o g^{-1} is continuous on GL(V) x G(V, m), Federer 2.7.16,
    p. 134 (composition and inversion are continuous). Supporting
    lemma. *)
Lemma linear_grassmann_conjugate_continuous :
  continuous (fun q : GL * GR => (linear_grassmann_conjugate q.1 q.2 : HVV)).
Proof.
have hcomp := @hom_composition_continuous R V B hB n b hb.
have hval := @set_type_val_continuous HVV (linear_group hB hb).
have hinv : continuous inv := topological_group_inv_continuous
  (lch_group_topological (linear_group_operations_lch hB hb)).
have hPc := @grassmann_space_projection_continuous R U V C B hC hB m c n b hc hb.
have hp1 : continuous (fun q : GL * GR => ((set_val q.1 : HVV), (P q.2 : HVV))).
  apply: (@topological_pair_continuous (GL * GR)%type HVV HVV).
  - by move=> q; exact: continuous_comp (@first_projection_continuous GL GR q) (hval q.1).
  - by move=> q; exact: continuous_comp (@second_projection_continuous GL GR q) (hPc q.2).
have hp : continuous (fun q : GL * GR =>
    ((hom_comp (set_val q.1 : Hom V V) (P q.2) : HVV), (set_val (inv q.1) : HVV))).
  apply: (@topological_pair_continuous (GL * GR)%type HVV HVV).
  - by move=> q; exact: (continuous_comp (hp1 q) (hcomp _)).
  - move=> q.
    have h1 := @first_projection_continuous GL GR q.
    exact: (continuous_comp h1 (continuous_comp (hinv q.1) (hval (inv q.1)))).
by move=> q; exact: (continuous_comp (hp q) (hcomp _)).
Qed.

(** Source for [linear_grassmann_projection_continuous]: (g, W) |->
    P_{g[W]} is continuous, Federer 1.7.4, p. 30, supporting 2.7.16,
    p. 138: ||P_{g[W]} - P_{g_0[W_0]}|| <=
    2 ||g o P_W o g^{-1} - g_0 o P_{W_0} o g_0^{-1}||
    (grassmann_projection_difference_bound). Supporting lemma. *)
Lemma linear_grassmann_projection_continuous :
  continuous (fun q : GL * GR => (P (linear_grassmann_action q.1 q.2) : HVV)).
Proof.
move=> q0 A /hom_space_nbhs_operator [r hr hA].
have hr2 : 0 < r / (1 + 1) by rewrite divr_gt0 // addr_gt0 ?ltr01.
have hcc := linear_grassmann_conjugate_continuous.
have hN := hcc q0 _
  (hom_space_operator_ball_nbhs (linear_grassmann_conjugate q0.1 q0.2 : HVV) hr2).
apply: (@filterS _ _ (nbhs_filter q0) _ _ _ hN)=> q /= hq; apply: hA.
apply: le_lt_trans (grassmann_projection_difference_bound hC hB hc hb
  (@linear_grassmann_conjugate_mem q.1 q.2) (@linear_grassmann_conjugate_fixed q.1 q.2)
  (@linear_grassmann_conjugate_mem q0.1 q0.2) (@linear_grassmann_conjugate_fixed q0.1 q0.2)) _.
have h2 : (0 : R) < 1 + 1 by rewrite addr_gt0 ?ltr01.
by rewrite mulrC -ltr_pdivlMr.
Qed.

(** Source for [linear_grassmann_action_continuous]: the action of
    GL(n, R) on G(n, m) is continuous, Federer 2.7.1, p. 121, as used in
    2.7.16, p. 138. Supporting lemma, by the initial topology of
    G(n, m). *)
Lemma linear_grassmann_action_continuous :
  continuous (fun q : GL * GR => linear_grassmann_action q.1 q.2).
Proof. apply: continuous_comp_initial; exact: linear_grassmann_projection_continuous. Qed.

(** Source for [linear_grassmann_action_compatible]: A(gh, W) =
    A(g, A(h, W)), Federer 2.7.1, p. 121, for the action of GL(n, R) on
    G(n, m), 2.7.16, p. 138. Supporting lemma. *)
Lemma linear_grassmann_action_compatible (g h : GL) (W : GR) :
  linear_grassmann_action (mul g h) W = linear_grassmann_action g (linear_grassmann_action h W).
Proof.
apply: grassmann_ext=> y; rewrite !linear_grassmann_actionE (linear_group_mulE hG); split.
- move=> [w hw <-]; exists ((set_val h : Hom V V) w); first by exists w.
  by rewrite hom_compE.
- move=> [w' [w hw <-] <-]; exists w=> //; by rewrite hom_compE.
Qed.

(** Source for [linear_grassmann_action_orthogonal]: on O(n) the action
    of GL(n, R) is that of example (6), Federer 2.7.16, pp. 138–139.
    Supporting lemma. *)
Lemma linear_grassmann_action_orthogonal (s : O) (W : GR) :
  grassmann_action hC hB hc hb s W = linear_grassmann_action (set_val s) W.
Proof. by apply: grassmann_ext=> y; split. Qed.

(** Source for [linear_grassmann_action_transitive]: GL(n, R) acts
    transitively on G(n, m), Federer 2.7.16, p. 138, since its subgroup
    O(n) does (example (6), p. 139). Supporting lemma. *)
Lemma linear_grassmann_action_transitive (W1 W2 : GR) : exists g, linear_grassmann_action g W1 = W2.
Proof.
have [s hs] := @grassmann_action_transitive R U V C B hC hB m c n b hc hb W1 W2.
by exists (set_val s); rewrite -linear_grassmann_action_orthogonal.
Qed.

(** Source for [linear_grassmann_orbit_open]: the orbit maps of the
    action of GL(n, R) on G(n, m) are open, Federer 2.7.1, p. 121, for
    2.7.16, p. 138. Supporting lemma: the orbit maps of the subgroup
    O(n) are open (example (6), p. 139), and subgroup_orbit_open
    applies. *)
Lemma linear_grassmann_orbit_open (W : GR) : is_open_map (orbit_map linear_grassmann_action W).
Proof.
have [mulO [invO [eO hO]]] := orthogonal_group_restriction_exists hB hb.
have hGr := grassmann_space_homogeneous hC hc hO.
apply: (@subgroup_orbit_open GL GR mul inv unit linear_grassmann_action
  (lch_group_topological (linear_group_operations_lch hB hb)) linear_grassmann_action_compatible O
  (subgroup_unit (orthogonal_group_subgroup hB hb)) (grassmann_action hC hB hc hb)
  linear_grassmann_action_orthogonal).
exact: (homogeneous_orbit_open hGr).
Qed.

(** Source for [linear_grassmann_homogeneous]: G(n, m) is a homogeneous
    space of GL(n, R) through A(g, W) = g[W], Federer 2.7.1, p. 121, as
    presupposed in 2.7.16, example (4), p. 138. Direct formalisation;
    Federer gives no proof. *)
Theorem linear_grassmann_homogeneous : is_homogeneous_space mul linear_grassmann_action.
Proof.
split.
- exact: linear_grassmann_action_continuous.
- exact: linear_grassmann_action_compatible.
- exact: linear_grassmann_orbit_open.
- move=> W; apply/seteqP; split=> // W' _.
  have [g hg] := linear_grassmann_action_transitive W W'.
  by exists g.
Qed.

(** Source for [linear_grassmann_locally_compact]: G(n, m) is a locally
    compact Hausdorff space, the standing hypothesis of Federer 2.7.1,
    p. 121, for 2.7.16, p. 138. Supporting lemma. *)
Lemma linear_grassmann_locally_compact : hausdorff_space GR /\ locally_compact [set: GR].
Proof.
have hH := @grassmann_space_hausdorff R U V C B hC hB m c n b hc hb.
split=> //.
exact: (homogeneous_space_locally_compact (linear_group_operations_lch hB hb)
  linear_grassmann_homogeneous hH).
Qed.

(** Source for [linear_grassmann_isotropy]: "the isotropy group
    GL(n, R)^W is the group studied in (3)", Federer 2.7.16, p. 138:
    g[W] = W exactly when g maps W onto W. Direct formalisation, as an
    equality of subsets of GL(V). *)
Theorem linear_grassmann_isotropy (W : GR) :
  isotropy_subgroup linear_grassmann_action W = subspace_stabiliser hB hb (grassmann_val (W : G V m)).
Proof.
apply/seteqP; split=> g.
- move=> hg y; rewrite /isotropy_subgroup /= in hg.
  have h := linear_grassmann_actionE g W y; rewrite hg in h.
  exact: h.
- move=> hg; rewrite /isotropy_subgroup /=; apply: grassmann_ext=> y.
  rewrite linear_grassmann_actionE; split.
  + by move=> /(hg y).
  + by move=> hy; apply/(hg y).
Qed.

End LinearAction.

Arguments linear_grassmann_action {R U V C B} hC hB {m c n b} hc hb g W.
