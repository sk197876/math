(** Federer (1969), 2.7.16, printed p. 140, example (7): "Suppose G is the
    group of all isometries (distance preserving transformations) of R^n.
    Then G^0 = G cap {g : g(0) = 0} = O(n), ... We infer that G = A(V, V)
    cap {g : L(g) in O(n)} = im tau o O(n)." The isometry group is the
    closed subgroup isometry_group of the affine group
    (AffineGroupTopology.v), whose members are the pairs (s, z) of an
    orthogonal member s of the linear group and a vector z, acting as tau_z
    o s. This module records the decomposition G = im tau o O(n) as a
    homeomorphism between O(n) x V and G, (s, z) |-> tau_z o s, expresses
    the multiplication, the inversion and the identity of G through those of
    O(n), and proves that V is a homogeneous space of G through the usual
    action (2.7.1, p. 121), with isotropy subgroup G^0 = {tau_z o s : z =
    0}. Here V is a space with an inner product and a finite basis; V = R^n
    is example (7). The group structures of G and O(n) are any restricted
    structures (is_subgroup_restriction). The local erratum has no entry for
    p. 140. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerNorm InnerMetric InnerNormedTopology LinearBasis TensorUP
  Hom HomInner OrthogonalMaps IsotropyGroupTopology TopologicalProductMaps TopologicalGroupUP
  TopologicalGroupLaws HomogeneousSpaceUP HomeomorphismUP HomSpaceTopology LinearGroupTopology
  LinearGroupSealed OrthogonalGroupTopology OrthogonalGroupHaarMeasure AffineGroupTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section IsometryGroup.
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
Local Notation O := (orthogonal_group hB hb).
Local Notation G := (isometry_group hB hb).
Local Notation om := (@orthogonal_element_map R V B hB n b hb).

(** Source for [isometry_linear]: the linear part L(g) in O(n) of an
    isometry g, "G = A(V, V) cap {g : L(g) in O(n)}", Federer 2.7.16,
    p. 140. Definition. *)
Definition isometry_linear (g : G) : O := exist _ (set_val g).1 (mem_set (set_valP g)).

(** Source for [isometry_translation]: the translation part g(0) of an
    isometry g = tau_{g(0)} o L(g), Federer 2.7.16, p. 140. Definition. *)
Definition isometry_translation (g : G) : VT := (set_val g).2.

(** Source for [isometry_of]: the isometry tau_z o s for s in O(n) and z
    in V, "G = im tau o O(n)", Federer 2.7.16, p. 140. Definition. *)
Definition isometry_of (s : O) (z : VT) : G :=
  exist _ (set_val s, z) (mem_set (set_valP s : isometry_group hB hb (set_val s, z))).

(** Source for [isometry_map]: an isometry g as a map of V,
    g(v) = g(0) + L(g)(v), Federer 2.7.16, pp. 133 and 140. Definition. *)
Definition isometry_map (g : G) (v : V) : V := isometry_translation g + om (isometry_linear g) v.

(** Source for [isometry_mapE]: the map of an isometry is that of the
    corresponding affine map tau_z o g, Federer 2.7.16, p. 134.
    Supporting lemma. *)
Lemma isometry_mapE (g : G) : isometry_map g = affine_group_map hB hb (set_val g).
Proof. by []. Qed.

(** Source for [isometry_of_linear]: L(tau_z o s) = s, Federer 2.7.16,
    p. 140. Supporting lemma. *)
Lemma isometry_of_linear (s : O) (z : VT) : isometry_linear (isometry_of s z) = s.
Proof. by apply: val_inj. Qed.

(** Source for [isometry_of_translation]: (tau_z o s)(0) = z, Federer
    2.7.16, p. 140. Supporting lemma. *)
Lemma isometry_of_translation (s : O) (z : VT) : isometry_translation (isometry_of s z) = z.
Proof. by []. Qed.

(** Source for [isometry_ofK]: every isometry is tau_{g(0)} o L(g),
    "G = im tau o O(n)", Federer 2.7.16, p. 140. Supporting lemma. *)
Lemma isometry_ofK (g : G) : isometry_of (isometry_linear g) (isometry_translation g) = g.
Proof. by apply: val_inj; case: g=> [[s z] h]. Qed.

(** Source for [isometry_of_mapE]: (tau_z o s)(v) = z + s(v), Federer
    2.7.16, p. 140. Supporting lemma. *)
Lemma isometry_of_mapE (s : O) (z : VT) v : isometry_map (isometry_of s z) v = z + om s v.
Proof. by []. Qed.

(** Source for [isometry_map_zero]: g(0) is the translation part of g,
    Federer 2.7.16, p. 140. Supporting lemma. *)
Lemma isometry_map_zero (g : G) : isometry_map g 0 = isometry_translation g.
Proof. by rewrite isometry_mapE affine_group_map_zero. Qed.

(** Source for [isometry_map_sub]: g(x) - g(y) = L(g)(x - y), Federer
    2.7.16, p. 133. Supporting lemma. *)
Lemma isometry_map_sub (g : G) x y : isometry_map g x - isometry_map g y = om (isometry_linear g) (x - y).
Proof.
rewrite /isometry_map opprD addrACA subrr add0r.
by rewrite (linearB (hom_as_linear (om (isometry_linear g)))).
Qed.

(** Source for [isometry_linear_map]: L(g)(v) = g(v) - g(0), Federer
    2.7.16, p. 133. Supporting lemma. *)
Lemma isometry_linear_map (g : G) v : om (isometry_linear g) v = isometry_map g v - isometry_map g 0.
Proof. by rewrite isometry_map_sub subr0. Qed.

(** Source for [isometry_ext]: an isometry is determined by its values,
    Federer 2.7.16, p. 133 (the isomorphism M). Supporting lemma. *)
Lemma isometry_ext (g h : G) : (forall v, isometry_map g v = isometry_map h v) -> g = h.
Proof. by move=> he; apply: val_inj; apply: affine_group_map_inj=> v; exact: he. Qed.

(** Source for [isometry_of_continuous]: (s, z) |-> tau_z o s is
    continuous from O(n) x V to G, Federer 2.7.16, pp. 134 and 140.
    Supporting lemma. *)
Lemma isometry_of_continuous : continuous (fun p : O * VT => isometry_of p.1 p.2).
Proof.
apply: set_type_continuous_into.
have -> : set_val \o (fun p : O * VT => isometry_of p.1 p.2) =
    (fun p : O * VT => ((set_val p.1 : GL), p.2)) by [].
apply: (@topological_pair_continuous (O * VT)%type GL VT).
- move=> p; exact: continuous_comp (@first_projection_continuous O VT p) (@set_type_val_continuous GL O _).
- exact: second_projection_continuous.
Qed.

(** Source for [isometry_linear_continuous]: g |-> L(g) is continuous
    from G to O(n), Federer 2.7.16, pp. 134 and 140. Supporting lemma. *)
Lemma isometry_linear_continuous : continuous isometry_linear.
Proof.
apply: set_type_continuous_into.
have -> : set_val \o isometry_linear = (@fst GL VT) \o (set_val : G -> AG) by [].
move=> g; apply: continuous_comp; first exact: set_type_val_continuous.
exact: first_projection_continuous.
Qed.

(** Source for [isometry_translation_continuous]: g |-> g(0) is
    continuous on G, Federer 2.7.16, pp. 134 and 140. Supporting lemma. *)
Lemma isometry_translation_continuous : continuous isometry_translation.
Proof.
move=> g; apply: (@continuous_comp G AG VT (set_val : G -> AG) (@snd GL VT)).
  exact: set_type_val_continuous.
exact: second_projection_continuous.
Qed.

(** Source for [isometry_product_homeomorphism]: "G = im tau o O(n)",
    Federer 2.7.16, p. 140, as a homeomorphism: (s, z) |-> tau_z o s is
    a homeomorphism of O(n) x V onto G with inverse g |-> (L(g), g(0)).
    Supporting theorem. *)
Theorem isometry_product_homeomorphism :
  is_homeomorphism_with_inverse (fun p : O * VT => isometry_of p.1 p.2)
    (fun g : G => (isometry_linear g, isometry_translation g)).
Proof.
split.
- exact: isometry_of_continuous.
- apply: (@topological_pair_continuous G O VT).
    exact: isometry_linear_continuous.
  exact: isometry_translation_continuous.
- by move=> [s z]; rewrite isometry_of_linear isometry_of_translation.
- by move=> g; exact: isometry_ofK.
Qed.

(** Source for [isometry_map_continuous]: (g, v) |-> g(v) is continuous
    on G x V, Federer 2.7.16, pp. 134 and 140. Supporting lemma. *)
Lemma isometry_map_continuous : continuous (fun p : G * VT => (isometry_map p.1 p.2 : VT)).
Proof.
have hA := homogeneous_action_continuous (affine_group_homogeneous hB hb).
move=> p; apply: (@continuous_comp (G * VT)%type (AG * VT)%type VT
  (fun p : G * VT => ((set_val p.1 : AG), p.2)) (fun q : AG * VT => affine_group_action hB hb q.1 q.2)).
  apply: (@topological_pair_continuous (G * VT)%type AG VT).
    move=> q; exact: continuous_comp (@first_projection_continuous G VT q) (@set_type_val_continuous AG _ _).
  exact: second_projection_continuous.
exact: hA.
Qed.

Variables (mulS : G -> G -> G) (invS : G -> G) (eS : G).
Hypothesis hS : is_subgroup_restriction (affine_group_mul hB hb) (affine_group_inv hB hb)
  (affine_group_unit hB hb) (isometry_group hB hb) mulS invS eS.
Variables (mulO : O -> O -> O) (invO : O -> O) (eO : O).
Hypothesis hO : is_subgroup_restriction (linear_group_mul hB hb) (linear_group_inv hB hb)
  (linear_group_unit hB hb) (orthogonal_group hB hb) mulO invO eO.

(** Source for [isometry_map_mul]: the multiplication of G is
    composition, Federer 2.7.16, pp. 134 and 140. Supporting lemma. *)
Lemma isometry_map_mul (g h : G) x : isometry_map (mulS g h) x = isometry_map g (isometry_map h x).
Proof. by rewrite !isometry_mapE (subgroup_restriction_mul hS) affine_group_map_mul. Qed.

(** Source for [isometry_map_unit]: the identity of G is 1_V, Federer
    2.7.16, p. 140. Supporting lemma. *)
Lemma isometry_map_unit x : isometry_map eS x = x.
Proof. by rewrite isometry_mapE (subgroup_restriction_unit hS) affine_group_map_unit. Qed.

(** Source for [isometry_map_inv]: g^{-1} is the inverse map of g,
    Federer 2.7.16, p. 140. Supporting lemma. *)
Lemma isometry_map_inv (g : G) :
  cancel (isometry_map g) (isometry_map (invS g)) /\ cancel (isometry_map (invS g)) (isometry_map g).
Proof. by rewrite !isometry_mapE (subgroup_restriction_inv hS); exact: affine_group_map_inv. Qed.

(** Source for [isometry_linear_mul]: L(g h) = L(g) o L(h), Federer
    2.7.16, p. 133. Supporting lemma. *)
Lemma isometry_linear_mul (g h : G) : isometry_linear (mulS g h) = mulO (isometry_linear g) (isometry_linear h).
Proof.
apply: orthogonal_element_ext=> v; rewrite (orthogonal_element_mulE hO) [LHS]isometry_linear_map.
by rewrite !isometry_map_mul isometry_map_sub -isometry_linear_map.
Qed.

(** Source for [isometry_linear_unit]: L(1_V) = 1_V, Federer 2.7.16,
    p. 133. Supporting lemma. *)
Lemma isometry_linear_unit : isometry_linear eS = eO.
Proof.
apply: orthogonal_element_ext=> v; rewrite (orthogonal_element_unit hO) isometry_linear_map.
by rewrite !isometry_map_unit subr0.
Qed.

(** Source for [isometry_translation_mul]: (g h)(0) = g(0) + L(g)(h(0)),
    Federer 2.7.16, p. 134. Supporting lemma. *)
Lemma isometry_translation_mul (g h : G) :
  isometry_translation (mulS g h) = isometry_translation g + om (isometry_linear g) (isometry_translation h).
Proof. by rewrite -[LHS]isometry_map_zero isometry_map_mul isometry_map_zero. Qed.

(** Source for [isometry_of_mul]: (tau_z o s)(tau_w o t) =
    tau_{z + s(w)} o (s o t), Federer 2.7.16, p. 134. Supporting lemma. *)
Lemma isometry_of_mul (s t : O) (z w : VT) :
  mulS (isometry_of s z) (isometry_of t w) = isometry_of (mulO s t) (z + om s w).
Proof.
apply: isometry_ext=> v; rewrite isometry_map_mul !isometry_of_mapE (orthogonal_element_mulE hO).
by rewrite (linearD (hom_as_linear (om s))) addrA.
Qed.

(** Source for [isometry_of_unit]: 1_V = tau_0 o 1_V, Federer 2.7.16,
    p. 134. Supporting lemma. *)
Lemma isometry_of_unit : eS = isometry_of eO 0.
Proof. by apply: isometry_ext=> v; rewrite isometry_map_unit isometry_of_mapE (orthogonal_element_unit hO) add0r. Qed.

(** Source for [isometry_linear_inv]: L(g^{-1}) = L(g)^{-1}, Federer
    2.7.16, p. 134. Supporting lemma. *)
Lemma isometry_linear_inv (g : G) : isometry_linear (invS g) = invO (isometry_linear g).
Proof.
have hOT := lch_group_topological (orthogonal_group_lch hO).
have hOG := topological_group_laws hOT.
apply: (group_inv_unique hOG); rewrite -isometry_linear_mul.
have -> : mulS g (invS g) = eS.
  apply: isometry_ext=> v; rewrite isometry_map_mul isometry_map_unit.
  exact: (isometry_map_inv g).2.
exact: isometry_linear_unit.
Qed.

(** Source for [isometry_point_action]: "the usual action of G on R^n",
    A(g, v) = g(v), Federer 2.7.16, pp. 138 and 140. Definition. *)
Definition isometry_point_action (g : G) (v : VT) : VT := isometry_map g v.

(** Source for [isometry_point_homogeneous]: V is a homogeneous space
    of the isometry group G through A(g, v) = g(v), Federer 2.7.16,
    p. 140, in the sense of 2.7.1, p. 121: A is continuous and
    compatible, the orbit map A^v maps a neighbourhood of tau_z o s of
    the form {tau_w o s : w in C} onto the open set s(v) + C, and
    tau_{y - v} maps v to y. Supporting theorem. *)
Theorem isometry_point_homogeneous : is_homogeneous_space mulS isometry_point_action.
Proof.
split.
- exact: isometry_map_continuous.
- by move=> g h v; exact: isometry_map_mul.
- move=> v U hU; rewrite openE=> y [g hgU <-]; rewrite /interior.
  pose s := isometry_linear g; pose z := isometry_translation g.
  have hU' : open ((fun p : O * VT => isometry_of p.1 p.2) @^-1` U).
    by apply: open_comp hU=> p _; exact: isometry_of_continuous.
  have hp : ((fun p : O * VT => isometry_of p.1 p.2) @^-1` U) (s, z) by rewrite /= isometry_ofK.
  have [[A C] [hA hC] hAC] : nbhs (s, z) ((fun p : O * VT => isometry_of p.1 p.2) @^-1` U).
    by apply: open_nbhs_nbhs; split.
  pose w : VT := om s v.
  have hCw : nbhs (z + w) ((fun y' : VT => y' - w) @^-1` C).
    move: hC=> /nbhs_ballP [r hr hCr]; apply/nbhs_ballP; exists r=> // y' hy'; apply: hCr.
    by move: hy'; rewrite -!ball_normE /= opprB addrA.
  have hyw : orbit_map isometry_point_action v g = z + w by [].
  rewrite hyw; apply: (@filterS _ _ (nbhs_filter _) _ _ _ hCw)=> y' /= hy'.
  exists (isometry_of s (y' - w)).
    by have := hAC (s, y' - w); apply; split=> //; exact: nbhs_singleton hA.
  by rewrite /orbit_map /isometry_point_action isometry_of_mapE subrK.
- move=> v; apply/seteqP; split=> // y _.
  exists (isometry_of eO (y - v))=> //.
  by rewrite /orbit_map /isometry_point_action isometry_of_mapE (orthogonal_element_unit hO) subrK.
Qed.

(** Source for [isometry_point_isotropy_origin]: "G^0 = G cap
    {g : g(0) = 0}", Federer 2.7.16, p. 140: the isotropy subgroup of 0
    consists of the isometries with translation part 0. Supporting
    lemma. *)
Lemma isometry_point_isotropy_origin :
  isotropy_subgroup isometry_point_action 0 = [set g | isometry_translation g = 0].
Proof.
by apply/seteqP; split=> g; rewrite /isotropy_subgroup /isometry_point_action /= isometry_map_zero.
Qed.

End IsometryGroup.

Arguments isometry_linear {R V B hB n b hb} g.
Arguments isometry_translation {R V B hB n b hb} g.
Arguments isometry_of {R V B hB n b hb} s z.
Arguments isometry_map {R V B hB n b hb} g v.
Arguments isometry_point_action {R V B hB n b hb} g v.
