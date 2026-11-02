(** Federer (1969), 2.7.16, printed pp. 133–134: "Using the maps L, M, tau
    we infer that functional composition is a continuous operation in A(V,
    V), and that inversion is continuous on the affine group of V, the open
    dense subset of univalent maps in A(V, V), which equals L^{-1}(linear
    group of V)", with M: A(V, V) ~ Hom(V, V) (+) V, M(f) = (L(f), f(0)),
    and M^{-1}(g, z) = tau_z o g. Here V is a space with an inner product
    and a finite basis. The affine group of V is represented through M by
    the pairs (g, z) of a member g of the linear group of V
    (LinearGroupTopology.v) and a vector z, with the product topology of the
    relative topology of the linear group in Hom(V, V) and the topology of
    V; affine_group_map (g, z) = tau_z o g is the univalent affine map with
    L = g and value z at 0, and every univalent affine map arises from
    exactly one pair. The multiplication (g, z)(h, w) = (g o h, z + g(w))
    and the inversion (g, z)^{-1} = (g^{-1}, -g^{-1}(z)) correspond to
    composition and inversion of maps. The affine group is a locally compact
    Hausdorff topological group (2.7.1, p. 121), and V is a homogeneous
    space of it through the usual action A((g, z), v) = z + g(v), used in
    examples (5) and (7), pp. 138 and 140. That all norms on A(V, V) induce
    the same topology is not formalised; the topology is the one transported
    by M. Example (7), p. 140: "Suppose G is the group of all isometries
    (distance preserving transformations) of R^n. Then G^0 = G cap {g : g(0)
    = 0} = O(n) ... We infer that G = A(V, V) cap {g : L(g) in O(n)} = im
    tau o O(n)." The isometry group is the closed subgroup of pairs (g, z)
    with g orthogonal; a map of V is distance preserving if and only if it
    is tau_z o g for such a pair, and a distance preserving map fixing 0 is
    an orthogonal linear map. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities InnerMetric
  InnerNormedTopology InnerBoundedness InnerFiniteCompactness LinearBasis TensorUP Hom HomInner
  OrthogonalMaps SubtypeCompactHausdorff IsotropyGroupTopology TopologicalProductMaps
  TopologicalGroupUP TopologicalGroupLaws HomogeneousSpaceUP HomeomorphismUP AffineMaps
  HomSpaceTopology LinearGroupTopology LinearGroupSealed OrthogonalGroupTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ProductSpaces.
Variables X Y : topologicalType.

(** Source for [product_hausdorff]: the product of two Hausdorff spaces
    is Hausdorff, supporting "the topological assumptions of our general
    theory are satisfied" for the affine group, Federer 2.7.16, p. 134.
    Supporting lemma. *)
Lemma product_hausdorff : hausdorff_space X -> hausdorff_space Y -> hausdorff_space (X * Y)%type.
Proof.
move=> hX hY [a x] [c y] hcl.
have h1 : a = c.
  apply: hX=> A C hA hC.
  have hA' : nbhs (a, x) (A `*` setT) by exists (A, setT)=> //; split=> //; exact: filterT.
  have hC' : nbhs (c, y) (C `*` setT) by exists (C, setT)=> //; split=> //; exact: filterT.
  have [[p q] [[hpA _] [hpC _]]] := hcl _ _ hA' hC'.
  by exists p.
have h2 : x = y.
  apply: hY=> A C hA hC.
  have hA' : nbhs (a, x) (setT `*` A) by exists (setT, A)=> //; split=> //; exact: filterT.
  have hC' : nbhs (c, y) (setT `*` C) by exists (setT, C)=> //; split=> //; exact: filterT.
  have [[p q] [[_ hqA] [_ hqC]]] := hcl _ _ hA' hC'.
  by exists q.
by rewrite h1 h2.
Qed.

(** Source for [product_locally_compact]: the product of two locally
    compact spaces is locally compact; a product of compact closed
    neighbourhoods is a compact closed neighbourhood. Supporting lemma
    for Federer 2.7.16, p. 134. *)
Lemma product_locally_compact :
  locally_compact [set: X] -> locally_compact [set: Y] -> locally_compact [set: (X * Y)%type].
Proof.
move=> hX hY [a x] _.
have [A hA [hAc hAcl]] := hX a I; rewrite withinET in hA.
have [C hC [hCc hCcl]] := hY x I; rewrite withinET in hC.
rewrite withinET; exists (A `*` C); last split.
- by exists (A, C).
- exact: compact_setX.
- have -> : A `*` C = (@fst X Y @^-1` A) `&` (@snd X Y @^-1` C) by [].
  apply: closedI.
  + by apply: preimage_closed hAcl=> p _; exact: first_projection_continuous.
  + by apply: preimage_closed hCcl=> p _; exact: second_projection_continuous.
Qed.

End ProductSpaces.

Section InnerSpace.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Local Notation VT := (inner_metric_space hB).

(** Source for [inner_space_hausdorff]: V is Hausdorff, being a metric
    space by 1.7.1, p. 28, as required in Federer 2.7.16, p. 134.
    Supporting lemma. *)
Lemma inner_space_hausdorff : hausdorff_space VT.
Proof. exact: (@metric_hausdorff R [the metricType R of VT]). Qed.

(** Source for [inner_space_locally_compact]: V is locally compact,
    since closed balls are compact by 1.7.1, p. 28; supporting Federer
    2.7.16, p. 134. Supporting lemma. *)
Lemma inner_space_locally_compact : locally_compact [set: VT].
Proof.
move=> x _; rewrite withinET; exists [set y : VT | `|y - x| <= 1].
  apply: (@filterS _ _ _ (ball x 1)); last exact: nbhsx_ballx.
  by move=> y; rewrite -ball_normE /= distrC=> h; exact: ltW.
have he : [set y : VT | `|y - x| <= 1] = closed_ball_ Num.norm x 1.
  by apply/seteqP; split=> y /=; rewrite /closed_ball_ distrC.
split; last by rewrite he; exact: closed_closed_ball_.
apply: (@inner_finite_basis_boundedly_compact R V B hB n b hb).
- by rewrite he; exact: closed_closed_ball_.
- exists (`|x| + 1)=> y hy.
  have h := ler_normD (y - x) x.
  rewrite subrK in h; apply: (le_trans h); rewrite addrC lerD2l.
  exact: hy.
Qed.

End InnerSpace.

Section AffineGroup.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Local Notation H := (inner_metric_space (hom_inner_productP hB hB hb)).
Local Notation VT := (inner_metric_space hB).
Local Notation GL := (set_type (linear_group hB hb)).
Local Notation AG := (GL * VT)%type.
Local Notation mul := (linear_group_mul hB hb).
Local Notation inv := (linear_group_inv hB hb).
Local Notation unit := (linear_group_unit hB hb).
Local Notation hG := (linear_group_operations hB hb).
Local Notation hGt := (lch_group_topological (linear_group_operations_lch hB hb)).
Local Notation N := (inner_norm hB).

(** Source for [affine_group_map]: M^{-1}(g, z) = tau_z o g, Federer
    2.7.16, p. 134: the univalent affine map with linear part g and
    value z at 0 corresponding to the pair (g, z). Definition. *)
Definition affine_group_map (p : AG) (v : V) : V := p.2 + (set_val p.1 : Hom V V) v.

(** Source for [affine_group_mapE]: M^{-1}(g, z) = tau_z o g, Federer
    2.7.16, p. 134. Supporting lemma. *)
Lemma affine_group_mapE (p : AG) :
  affine_group_map p = affine_translation p.2 \o (set_val p.1 : Hom V V).
Proof. by []. Qed.

(** Source for [affine_group_map_affine]: tau_z o g belongs to A(V, V),
    Federer 2.7.16, p. 133. Supporting lemma. *)
Lemma affine_group_map_affine (p : AG) : is_affine_map (affine_group_map p).
Proof.
move=> x y s t hst; rewrite /affine_group_map.
have -> : (set_val p.1 : Hom V V) (s *: x + t *: y) =
    s *: (set_val p.1 : Hom V V) x + t *: (set_val p.1 : Hom V V) y.
  by rewrite linearD !linearZ_LR.
by rewrite !scalerDr addrACA -scalerDl hst scale1r.
Qed.

(** Source for [affine_group_map_zero]: M(tau_z o g) has second
    component z, Federer 2.7.16, p. 133. Supporting lemma. *)
Lemma affine_group_map_zero (p : AG) : affine_group_map p 0 = p.2.
Proof.
rewrite /affine_group_map.
have -> : (set_val p.1 : Hom V V) 0 = 0 by exact: (linear0 (hom_as_linear (set_val p.1 : Hom V V))).
by rewrite addr0.
Qed.

(** Source for [affine_group_map_linear_part]: L(tau_z o g) = g,
    Federer 2.7.16, p. 133. Supporting lemma. *)
Lemma affine_group_map_linear_part (p : AG) :
  affine_linear_part (affine_group_map p) =1 (set_val p.1 : Hom V V).
Proof. by move=> v; rewrite /affine_linear_part affine_group_map_zero /affine_group_map addrC addKr. Qed.

(** Source for [affine_group_map_univalent]: tau_z o g is univalent,
    Federer 2.7.16, p. 134. Supporting lemma. *)
Lemma affine_group_map_univalent (p : AG) : injective (affine_group_map p).
Proof. by move=> x y; rewrite /affine_group_map=> /addrI; exact: (set_valP p.1). Qed.

(** Source for [affine_group_map_inj]: M is univalent: tau_z o g
    determines (g, z), Federer 2.7.16, p. 133. Supporting lemma. *)
Lemma affine_group_map_inj (p q : AG) : affine_group_map p =1 affine_group_map q -> p = q.
Proof.
case: p q=> [g z] [h w] he.
have hz : z = w by have := he 0; rewrite !affine_group_map_zero.
have hgh : g = h.
  apply: val_inj; apply: hom_ext=> v.
  by rewrite -(affine_group_map_linear_part (g, z)) -(affine_group_map_linear_part (h, w))
    /affine_linear_part !he.
by rewrite hz hgh.
Qed.

(** Source for [affine_group_map_onto]: "the affine group of V, the ...
    subset of univalent maps in A(V, V), which equals L^{-1}(linear group
    of V)", Federer 2.7.16, p. 134: every univalent affine map is
    tau_z o g for a member g of the linear group. Direct formalisation. *)
Theorem affine_group_map_onto (f : V -> V) : is_affine_map f -> injective f ->
  exists p : AG, affine_group_map p = f.
Proof.
move=> haf hif.
have hl := affine_linear_part_linear haf.
pose g : Hom V V := @HomMap R V V (affine_linear_part f) (introT (asboolP _) hl).
have hg : linear_group hB hb (g : H) by exact: (affine_univalent_iff f).1 hif.
exists (exist _ (g : H) (mem_set hg), f 0).
by apply: funext=> v; rewrite /affine_group_map /= /affine_linear_part addrC subrK.
Qed.

(** Source for [affine_group_mul]: the multiplication of the affine
    group, functional composition carried by M: (g, z)(h, w) =
    (g o h, z + g(w)), since tau_z o g o tau_w o h = tau_{z + g(w)} o g o h,
    Federer 2.7.16, pp. 133–134. Definition. *)
Definition affine_group_mul (p q : AG) : AG := (mul p.1 q.1, p.2 + (set_val p.1 : Hom V V) q.2).

(** Source for [affine_group_inv]: the inversion of the affine group,
    (g, z)^{-1} = (g^{-1}, -g^{-1}(z)), Federer 2.7.16, p. 134.
    Definition. *)
Definition affine_group_inv (p : AG) : AG := (inv p.1, - (set_val (inv p.1) : Hom V V) p.2).

(** Source for [affine_group_unit]: the identity (1_V, 0) of the affine
    group, Federer 2.7.16, p. 134. Definition. *)
Definition affine_group_unit : AG := (unit, 0).

(** Source for [affine_group_map_mul]: M^{-1} carries the multiplication
    to functional composition, Federer 2.7.16, p. 134. Supporting
    lemma. *)
Lemma affine_group_map_mul (p q : AG) :
  affine_group_map (affine_group_mul p q) = affine_group_map p \o affine_group_map q.
Proof.
apply: funext=> v; rewrite /affine_group_map /= (linear_group_mulE hG) hom_compE.
have -> : (set_val p.1 : Hom V V) (q.2 + (set_val q.1 : Hom V V) v) =
    (set_val p.1 : Hom V V) q.2 + (set_val p.1 : Hom V V) ((set_val q.1 : Hom V V) v).
  exact: (linearD (hom_as_linear (set_val p.1 : Hom V V))).
by rewrite addrA.
Qed.

(** Source for [affine_group_map_unit]: M^{-1}(1_V, 0) = 1_V, Federer
    2.7.16, p. 134. Supporting lemma. *)
Lemma affine_group_map_unit : affine_group_map affine_group_unit = id.
Proof. by apply: funext=> v; rewrite /affine_group_map /= (linear_group_unitE hG) add0r. Qed.

(** Source for [affine_group_map_inv]: M^{-1} carries the inversion to
    the inverse map, Federer 2.7.16, p. 134. Supporting lemma. *)
Lemma affine_group_map_inv (p : AG) :
  cancel (affine_group_map p) (affine_group_map (affine_group_inv p)) /\
  cancel (affine_group_map (affine_group_inv p)) (affine_group_map p).
Proof.
have [hgi hig] := linear_group_inv_cancel hG p.1.
have hl (f : Hom V V) x y : f (x + y) = f x + f y by exact: (linearD (hom_as_linear f)).
have hn (f : Hom V V) x : f (- x) = - f x by exact: (linearN (hom_as_linear f)).
split=> v; rewrite /affine_group_map /=.
- by rewrite hl hgi addrA addNr add0r.
- by rewrite hl hn hig addrA subrr add0r.
Qed.

(** Source for [affine_group_laws]: the group laws of the affine group,
    Federer 2.7.16, p. 134, as required in 2.7.1, p. 121. Supporting
    lemma. *)
Lemma affine_group_laws : is_group_laws affine_group_mul affine_group_inv affine_group_unit.
Proof.
have hgl := linear_group_group_laws hG.
split.
- move=> p q r; apply: affine_group_map_inj=> v.
  by rewrite !affine_group_map_mul.
- move=> p; apply: affine_group_map_inj=> v.
  by rewrite affine_group_map_mul affine_group_map_unit.
- move=> p; apply: affine_group_map_inj=> v.
  rewrite affine_group_map_mul affine_group_map_unit /=.
  exact: (affine_group_map_inv p).1.
Qed.

(** Source for [hom_evaluation_continuous_comp]: if F and G are
    continuous, so is t |-> F(t)(G(t)), by the continuity of evaluation;
    supporting Federer 2.7.16, p. 134. *)
Lemma hom_evaluation_continuous_comp (T : topologicalType) (F : T -> H) (G : T -> VT) :
  continuous F -> continuous G -> continuous (fun t => ((F t : Hom V V) (G t) : VT)).
Proof.
move=> hF hGc t.
apply: (@continuous_comp T (H * VT)%type VT (fun t => (F t, G t))
  (fun q : H * VT => ((q.1 : Hom V V) q.2 : VT))).
  exact: (@topological_pair_continuous T H VT F G hF hGc).
exact: (@hom_evaluation_continuous R V V B B hB hB n b hb).
Qed.

(** Source for [affine_group_mul_continuous]: "functional composition is
    a continuous operation", Federer 2.7.16, p. 134, for the affine
    group: ((g, z), (h, w)) |-> (g o h, z + g(w)) is continuous.
    Supporting lemma. *)
Lemma affine_group_mul_continuous : continuous (fun p : AG * AG => affine_group_mul p.1 p.2).
Proof.
apply: (@topological_pair_continuous (AG * AG)%type GL VT).
- move=> pq; apply: (@continuous_comp (AG * AG)%type (GL * GL)%type GL
    (fun pq : AG * AG => (pq.1.1, pq.2.1)) (fun r : GL * GL => mul r.1 r.2)).
    apply: (@topological_pair_continuous (AG * AG)%type GL GL).
    + move=> r; exact: (continuous_comp (@first_projection_continuous AG AG r)
        (@first_projection_continuous GL VT _)).
    + move=> r; exact: (continuous_comp (@second_projection_continuous AG AG r)
        (@first_projection_continuous GL VT _)).
  exact: (topological_group_mul_continuous hGt).
- move=> pq; apply: (@continuous_comp (AG * AG)%type (VT * VT)%type VT
    (fun pq : AG * AG => (pq.1.2, ((set_val pq.1.1 : H) : Hom V V) pq.2.2))
    (fun r : VT * VT => r.1 + r.2)); last exact: add_continuous.
  apply: (@topological_pair_continuous (AG * AG)%type VT VT).
  + move=> r; exact: (continuous_comp (@first_projection_continuous AG AG r)
      (@second_projection_continuous GL VT _)).
  + apply: hom_evaluation_continuous_comp.
    * move=> r; apply: (@continuous_comp _ _ _ (@fst AG AG) (fun p : AG => (set_val p.1 : H)) r
        (@first_projection_continuous AG AG r)).
      apply: (@continuous_comp _ _ _ (@fst GL VT) (fun g : GL => (set_val g : H)));
        first exact: first_projection_continuous.
      exact: set_type_val_continuous.
    * move=> r; exact: (continuous_comp (@second_projection_continuous AG AG r)
        (@second_projection_continuous GL VT _)).
Qed.

(** Source for [affine_group_inv_continuous]: "inversion is continuous
    on the affine group of V", Federer 2.7.16, p. 134: (g, z) |->
    (g^{-1}, -g^{-1}(z)) is continuous. Supporting lemma. *)
Lemma affine_group_inv_continuous : continuous affine_group_inv.
Proof.
have hi := topological_group_inv_continuous hGt.
apply: (@topological_pair_continuous AG GL VT).
- move=> p; exact: (continuous_comp (@first_projection_continuous GL VT p) (hi _)).
- move=> p; apply: (@continuous_comp AG VT VT
    (fun p : AG => ((set_val (inv p.1) : H) : Hom V V) p.2) (fun v : VT => - v)); last exact: oppr_continuous.
  apply: hom_evaluation_continuous_comp; last exact: second_projection_continuous.
  move=> q; apply: (@continuous_comp _ _ _ (@fst GL VT) (fun g : GL => (set_val (inv g) : H)) q
    (@first_projection_continuous GL VT q)).
  apply: (@continuous_comp _ _ _ inv (fun g : GL => (set_val g : H))); first exact: hi.
  exact: set_type_val_continuous.
Qed.

(** Source for [affine_group_lch]: "the topological assumptions of our
    general theory are satisfied", Federer 2.7.16, p. 134, for the affine
    group of V: with the operations carried by M and the product
    topology, it is a locally compact Hausdorff topological group in the
    sense of 2.7.1, p. 121. Direct formalisation. *)
Theorem affine_group_lch : is_locally_compact_hausdorff_group affine_group_mul affine_group_inv affine_group_unit.
Proof.
have hl := linear_group_operations_lch hB hb.
split.
- split; [exact: affine_group_laws|exact: affine_group_mul_continuous|exact: affine_group_inv_continuous].
- apply: product_hausdorff; first exact: (lch_group_hausdorff hl).
  exact: inner_space_hausdorff.
- apply: product_locally_compact; first exact: (lch_group_locally_compact hl).
  exact: inner_space_locally_compact hb.
Qed.

(** Source for [affine_group_action]: "the usual action of G on R^n",
    Federer 2.7.16, p. 138, example (5): A((g, z), v) = z + g(v), the
    value at v of tau_z o g. Definition. *)
Definition affine_group_action (p : AG) (v : VT) : VT := affine_group_map p v.

(** Source for [affine_group_homogeneous]: V is a homogeneous space of
    the affine group through A((g, z), v) = z + g(v), Federer 2.7.16,
    pp. 138 and 140, in the sense of 2.7.1, p. 121: A is continuous and
    compatible with the multiplication, A^v maps an open neighbourhood
    A x C of (g, z) onto a set containing the open set g(v) + C, and
    (1_V, y - v) maps v to y. Direct formalisation. *)
Theorem affine_group_homogeneous : is_homogeneous_space affine_group_mul affine_group_action.
Proof.
split.
- move=> p0; apply: (@continuous_comp (AG * VT)%type (VT * VT)%type VT
    (fun p : AG * VT => (p.1.2, ((set_val p.1.1 : H) : Hom V V) p.2))
    (fun r : VT * VT => r.1 + r.2)); last exact: add_continuous.
  apply: (@topological_pair_continuous (AG * VT)%type VT VT).
  + move=> r; exact: (continuous_comp (@first_projection_continuous AG VT r)
      (@second_projection_continuous GL VT _)).
  + apply: hom_evaluation_continuous_comp; last exact: second_projection_continuous.
    move=> r; apply: (@continuous_comp _ _ _ (@fst AG VT) (fun p : AG => (set_val p.1 : H)) r
      (@first_projection_continuous AG VT r)).
    apply: (@continuous_comp _ _ _ (@fst GL VT) (fun g : GL => (set_val g : H)));
      first exact: first_projection_continuous.
    exact: set_type_val_continuous.
- by move=> p q v; rewrite /affine_group_action affine_group_map_mul.
- move=> v U hU; rewrite openE=> y [[g z] hU' <-]; rewrite /interior.
  have [[A C] [hA hC] hAC] : nbhs (g, z) U by apply: open_nbhs_nbhs; split.
  pose w : VT := (set_val g : Hom V V) v.
  have hCw : nbhs (z + w) ((fun y' : VT => y' - w) @^-1` C).
    move: hC=> /nbhs_ballP [e he hCe]; apply/nbhs_ballP; exists e=> // y' hy'; apply: hCe.
    by move: hy'; rewrite -!ball_normE /= opprB addrA.
  apply: (@filterS _ _ (nbhs_filter _) _ _ _ hCw)=> y' /= hy'.
  exists (g, y' - w); first by apply: hAC; split=> //; exact: nbhs_singleton hA.
  by rewrite /orbit_map /affine_group_action /affine_group_map /= subrK.
- move=> v; apply/seteqP; split=> // y _.
  exists (unit, y - v)=> //.
  by rewrite /orbit_map /affine_group_action /affine_group_map /= (linear_group_unitE hG) subrK.
Qed.

(** Source for [affine_group_isotropy_origin]: "with G^0 = GL(n, R)",
    Federer 2.7.16, p. 138, example (5): the isotropy subgroup of 0 for
    the usual action of the affine group consists of the pairs (g, 0),
    that is, of the linear automorphisms. Supporting lemma. *)
Lemma affine_group_isotropy_origin :
  isotropy_subgroup affine_group_action 0 = [set p : AG | p.2 = 0].
Proof.
apply/seteqP; split=> p; rewrite /isotropy_subgroup /affine_group_action /=;
  by rewrite affine_group_map_zero.
Qed.

(** Source for [affine_group_translations_commute]: "ker L|G = im tau
    is abelian", Federer 2.7.16, p. 138, example (5): the pairs (1_V, z),
    corresponding to the translations tau_z, commute. Supporting lemma. *)
Lemma affine_group_translations_commute (p q : AG) :
  p.1 = unit -> q.1 = unit -> affine_group_mul p q = affine_group_mul q p.
Proof.
case: p q=> [g z] [h w] /= -> ->; rewrite /affine_group_mul /= (linear_group_unitE hG).
by rewrite addrC.
Qed.

(** Source for [isometry_group]: "the group of all isometries (distance
    preserving transformations) of R^n ... G = A(V, V) cap
    {g : L(g) in O(n)} = im tau o O(n)", Federer 2.7.16, p. 140, example
    (7): the pairs (g, z) with g orthogonal. Definition. *)
Definition isometry_group : set AG := [set p | orthogonal_group hB hb p.1].

(** Source for [isometry_group_maps]: Federer 2.7.16, p. 140, example
    (7): a map f of V is distance preserving if and only if it is
    tau_z o g with g orthogonal, "G = A(V, V) cap {g : L(g) in O(n)} =
    im tau o O(n)"; g = f - f(0) preserves inner products and is linear
    (distance_preserving_inner, inner_preserving_linear). Direct
    formalisation. *)
Theorem isometry_group_maps (f : V -> V) :
  (forall x y, N (f x - f y) = N (x - y)) <-> exists2 p, isometry_group p & affine_group_map p = f.
Proof.
split.
- move=> hf.
  pose g (v : V) : V := f v - f 0.
  have hg x y : N (g x - g y) = N (x - y) by rewrite /g opprB addrA subrK hf.
  have hg0 : g 0 = 0 by rewrite /g subrr.
  have hgi := distance_preserving_inner hg hg0.
  have hgl := inner_preserving_linear hB hgi.
  pose gh : Hom V V := @HomMap R V V g (introT (asboolP _) hgl).
  have hgo : is_orthogonal_map B B (hom_as_linear gh) by exact: hgi.
  have hgG : linear_group hB hb (gh : H) by exact: (orthogonal_map_injective hB hB hgo).
  exists (exist _ (gh : H) (mem_set hgG), f 0); first exact: hgo.
  by apply: funext=> v; rewrite /affine_group_map /= /g addrC subrK.
- move=> [p hp <-] x y; rewrite /affine_group_map opprD addrACA subrr add0r.
  have -> : (set_val p.1 : Hom V V) x - (set_val p.1 : Hom V V) y = (set_val p.1 : Hom V V) (x - y).
    by rewrite (linearB (hom_as_linear (set_val p.1 : Hom V V))).
  exact: (orthogonal_map_norm hB hB hp).
Qed.

(** Source for [isometry_isotropy_orthogonal]: "G^0 = G cap
    {g : g(0) = 0} = O(n)", Federer 2.7.16, p. 140, example (7): a
    distance preserving map fixing 0 is an orthogonal member of the
    linear group. Direct formalisation. *)
Theorem isometry_isotropy_orthogonal (f : V -> V) :
  (forall x y, N (f x - f y) = N (x - y)) -> f 0 = 0 ->
  exists2 g : GL, orthogonal_group hB hb g & f = (set_val g : Hom V V).
Proof.
move=> hf h0; have [[g z] hp he] := (isometry_group_maps f).1 hf.
have hz : z = 0 by rewrite -h0 -he affine_group_map_zero.
exists g=> //; rewrite -he; apply: funext=> v.
by rewrite /affine_group_map /= hz add0r.
Qed.

(** Source for [isometry_group_closed]: the isometry group is closed in
    the affine group, Federer 2.7.16, p. 140, since O(n) is closed in
    GL(n, R). Supporting lemma. *)
Lemma isometry_group_closed : closed isometry_group.
Proof.
apply: preimage_closed; last exact: orthogonal_group_closed.
by move=> p _; exact: first_projection_continuous.
Qed.

(** Source for [isometry_group_subgroup]: the isometries form a
    subgroup of the affine group, Federer 2.7.16, p. 140. Supporting
    lemma. *)
Lemma isometry_group_subgroup :
  is_subgroup affine_group_mul affine_group_inv affine_group_unit isometry_group.
Proof.
have hO := orthogonal_group_subgroup hB hb.
split.
- exact: (subgroup_unit hO).
- by move=> p q hp hq; exact: (subgroup_mul hO hp hq).
- by move=> p hp; exact: (subgroup_inv hO hp).
Qed.

(** Source for [isometry_group_restriction_exists]: the isometry group
    of Federer 2.7.16, p. 140, is a group with the operations of the
    affine group. Existence of the restricted operations. *)
Theorem isometry_group_restriction_exists :
  exists mulS invS eS,
    is_subgroup_restriction affine_group_mul affine_group_inv affine_group_unit isometry_group mulS invS eS.
Proof. exact: subgroup_restriction_exists isometry_group_subgroup. Qed.

(** Source for [isometry_group_lch]: the isometry group, a closed
    subgroup of the affine group, is a locally compact Hausdorff
    topological group, Federer 2.7.16, p. 140, with 2.7.1, p. 121.
    Direct formalisation. *)
Theorem isometry_group_lch mulS invS eS :
  is_subgroup_restriction affine_group_mul affine_group_inv affine_group_unit isometry_group mulS invS eS ->
  is_locally_compact_hausdorff_group mulS invS eS.
Proof.
move=> hS; apply: (subgroup_restriction_locally_compact_hausdorff hS); last exact: isometry_group_closed.
exact: affine_group_lch.
Qed.

End AffineGroup.

Arguments affine_group_mul {R V B} hB {n b} hb.
Arguments affine_group_inv {R V B} hB {n b} hb.
Arguments affine_group_unit {R V B} hB {n b} hb.
Arguments affine_group_map {R V B} hB {n b} hb.
Arguments affine_group_action {R V B} hB {n b} hb.
Arguments isometry_group {R V B} hB {n b} hb.
