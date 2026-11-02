(** Federer (1969), 2.7.1, printed pp. 121–122: consequences of the
    specification of a topological group in TopologicalGroupUP.v. The
    two-sided group laws, the inverse of a product, cancellation, the
    description of the left cosets g S of a subgroup S, and the fact that
    translations and inversion are homeomorphisms are used throughout 2.7.1
    (for instance in "(A_g)^{-1} = A_{g^{-1}}" and in the space G/S).
    Federer treats them as background. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import TopologicalProductMaps HomeomorphismUP TopologicalGroupUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Section GroupLaws.
Variable G : Type.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G).
Hypothesis hG : is_group_laws mul inv e.

(** Source for [group_mulgV]: g g^{-1} = e, supporting the group
    computations of Federer 2.7.1, pp. 121–122. The product
    k = g g^{-1} satisfies k k = k, and k = k^{-1}(k k) = e. *)
Lemma group_mulgV g : mul g (inv g) = e.
Proof.
have hk : mul (mul g (inv g)) (mul g (inv g)) = mul g (inv g).
  by rewrite -(group_mulA hG) [mul (inv g) (mul g (inv g))](group_mulA hG) (group_mulVg hG) (group_mul1g hG).
rewrite -[mul g (inv g)](group_mul1g hG) -[in X in mul X _](group_mulVg hG (mul g (inv g))).
by rewrite -(group_mulA hG) hk (group_mulVg hG).
Qed.

(** Source for [group_mulg1]: e is a right identity, supporting
    Federer 2.7.1, pp. 121–122. *)
Lemma group_mulg1 g : mul g e = g.
Proof. by rewrite -(group_mulVg hG g) (group_mulA hG) group_mulgV (group_mul1g hG). Qed.

(** Source for [group_mulKg]: g^{-1}(g h) = h, supporting Federer
    2.7.1, pp. 121–122. *)
Lemma group_mulKg g h : mul (inv g) (mul g h) = h.
Proof. by rewrite (group_mulA hG) (group_mulVg hG) (group_mul1g hG). Qed.

(** Source for [group_mulKVg]: g(g^{-1} h) = h, supporting Federer
    2.7.1, pp. 121–122. *)
Lemma group_mulKVg g h : mul g (mul (inv g) h) = h.
Proof. by rewrite (group_mulA hG) group_mulgV (group_mul1g hG). Qed.

(** Source for [group_mulgK]: (h g) g^{-1} = h, supporting Federer
    2.7.1, pp. 121–122. *)
Lemma group_mulgK g h : mul (mul h g) (inv g) = h.
Proof. by rewrite -(group_mulA hG) group_mulgV group_mulg1. Qed.

(** Source for [group_mulgKV]: (h g^{-1}) g = h, supporting Federer
    2.7.1, pp. 121–122. *)
Lemma group_mulgKV g h : mul (mul h (inv g)) g = h.
Proof. by rewrite -(group_mulA hG) (group_mulVg hG) group_mulg1. Qed.

(** Source for [group_inv_unique]: a right inverse is the inverse,
    supporting Federer 2.7.1, pp. 121–122. *)
Lemma group_inv_unique g h : mul g h = e -> h = inv g.
Proof. by move=> hgh; rewrite -(group_mulKg g h) hgh group_mulg1. Qed.

(** Source for [group_invK]: (g^{-1})^{-1} = g, supporting Federer
    2.7.1, pp. 121–122. *)
Lemma group_invK g : inv (inv g) = g.
Proof. by apply/esym/group_inv_unique; exact: (group_mulVg hG). Qed.

(** Source for [group_invM]: (g h)^{-1} = h^{-1} g^{-1}, supporting
    Federer 2.7.1, pp. 121–122. *)
Lemma group_invM g h : inv (mul g h) = mul (inv h) (inv g).
Proof.
apply/esym/group_inv_unique.
by rewrite -(group_mulA hG) [mul h (mul (inv h) (inv g))]group_mulKVg group_mulgV.
Qed.

(** Source for [group_inv1]: e^{-1} = e, supporting Federer 2.7.1,
    pp. 121–122. *)
Lemma group_inv1 : inv e = e.
Proof. by apply/esym/group_inv_unique; exact: (group_mul1g hG). Qed.

(** Source for [group_mul_left_cancel]: left cancellation, supporting
    Federer 2.7.1, pp. 121–122. *)
Lemma group_mul_left_cancel g h k : mul g h = mul g k -> h = k.
Proof. by move=> hgh; rewrite -(group_mulKg g h) hgh group_mulKg. Qed.

(** Source for [left_coset_member]: h belongs to g S if and only if
    g^{-1} h belongs to S, supporting the cosets of Federer 2.7.1,
    p. 122. No subgroup hypothesis is needed. *)
Lemma left_coset_member (S : set G) g h : left_coset mul g S h <-> S (mul (inv g) h).
Proof.
split.
- by case=> s hs <-; rewrite group_mulKg.
- by move=> hs; exists (mul (inv g) h)=> //; rewrite group_mulKVg.
Qed.

(** Source for [left_coset_eq]: g S = h S if and only if g^{-1} h
    belongs to S, for a subgroup S, supporting the identification of
    the points of G/S with cosets in Federer 2.7.1, p. 122. *)
Lemma left_coset_eq (S : set G) g h :
  is_subgroup mul inv e S -> left_coset mul g S = left_coset mul h S <-> S (mul (inv g) h).
Proof.
move=> hS; split.
- move=> hgh; apply/(left_coset_member S g h); rewrite hgh.
  by exists e; [exact: subgroup_unit hS|exact: group_mulg1].
- move=> hs; apply/seteqP; split=> k /(left_coset_member S) hk; apply/(left_coset_member S).
  + have -> : mul (inv h) k = mul (inv (mul (inv g) h)) (mul (inv g) k).
      by rewrite group_invM group_invK -(group_mulA hG) group_mulKVg.
    by apply: (subgroup_mul hS)=> //; exact: (subgroup_inv hS).
  + have -> : mul (inv g) k = mul (mul (inv g) h) (mul (inv h) k).
      by rewrite -(group_mulA hG) group_mulKVg.
    exact: (subgroup_mul hS).
Qed.

End GroupLaws.

Section TopologicalGroupMaps.
Variable G : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G).
Hypothesis hT : is_topological_group mul inv e.
(** Source for [hG]: the group laws of the topological group G,
    Federer 2.7.1, p. 121, used in this section. *)
Let hG := topological_group_laws hT.
(** Source for [hm]: continuity of the multiplication of G on G x G,
    Federer 2.7.1, p. 121, used in this section. *)
Let hm : continuous (fun p : G * G => mul p.1 p.2) := topological_group_mul_continuous hT.

(** Source for [left_translation_continuous]: h |-> g h is
    continuous, supporting Federer 2.7.1, pp. 121–122. *)
Lemma left_translation_continuous g : continuous (mul g).
Proof.
have hp : continuous (fun h : G => (g, h)).
  by apply: topological_pair_continuous; [exact: cst_continuous|move=> ?].
move=> h; have := continuous_comp (hp h) (@hm (g, h)); exact.
Qed.

(** Source for [right_translation_continuous]: h |-> h g is
    continuous, supporting Federer 2.7.1, pp. 121–122. *)
Lemma right_translation_continuous g : continuous (fun h => mul h g).
Proof.
have hp : continuous (fun h : G => (h, g)).
  by apply: topological_pair_continuous; [move=> ?|exact: cst_continuous].
move=> h; have := continuous_comp (hp h) (@hm (h, g)); exact.
Qed.

(** Source for [division_continuous]: (g,h) |-> g^{-1} h is
    continuous on G x G, supporting the space G/S of Federer 2.7.1,
    p. 122. *)
Lemma division_continuous : continuous (fun p : G * G => mul (inv p.1) p.2).
Proof.
have hp := @first_factor_map_continuous G G G inv (topological_group_inv_continuous hT).
move=> p; have := continuous_comp (hp p) (@hm (inv p.1, p.2)); exact.
Qed.

(** Source for [left_translation_homeomorphism]: left translation by
    g is a homeomorphism with inverse the left translation by g^{-1},
    supporting Federer 2.7.1, pp. 121–122. *)
Lemma left_translation_homeomorphism g : is_homeomorphism_with_inverse (mul g) (mul (inv g)).
Proof.
constructor; [exact: left_translation_continuous|exact: left_translation_continuous| |].
- by move=> h; exact: (group_mulKg hG).
- by move=> h; exact: (group_mulKVg hG).
Qed.

(** Source for [right_translation_homeomorphism]: right translation by
    g is a homeomorphism with inverse the right translation by g^{-1},
    supporting Federer 2.7.1, pp. 121–122. *)
Lemma right_translation_homeomorphism g :
  is_homeomorphism_with_inverse (fun h => mul h g) (fun h => mul h (inv g)).
Proof.
constructor; [exact: right_translation_continuous|exact: right_translation_continuous| |].
- by move=> h; exact: (group_mulgK hG).
- by move=> h; exact: (group_mulgKV hG).
Qed.

(** Source for [inversion_homeomorphism]: inversion is a
    homeomorphism equal to its own inverse, supporting Federer 2.7.1,
    pp. 121–122. *)
Lemma inversion_homeomorphism : is_homeomorphism_with_inverse inv inv.
Proof.
constructor; [exact: topological_group_inv_continuous hT|exact: topological_group_inv_continuous hT| |].
- by move=> g; exact: (group_invK hG).
- by move=> g; exact: (group_invK hG).
Qed.

(** Source for [left_translation_open_map]: left translations are
    open maps, supporting Federer 2.7.1, p. 122. *)
Lemma left_translation_open_map g : is_open_map (mul g).
Proof. exact: homeomorphism_with_inverse_open_map (left_translation_homeomorphism g). Qed.

(** Source for [right_translation_open_map]: right translations are
    open maps, supporting Federer 2.7.1, p. 122. *)
Lemma right_translation_open_map g : is_open_map (fun h => mul h g).
Proof. exact: homeomorphism_with_inverse_open_map (right_translation_homeomorphism g). Qed.

End TopologicalGroupMaps.

Arguments left_translation_continuous [G mul inv e] hT g _ _ _.
Arguments right_translation_continuous [G mul inv e] hT g _ _ _.
Arguments division_continuous [G mul inv e] hT _ _ _.
