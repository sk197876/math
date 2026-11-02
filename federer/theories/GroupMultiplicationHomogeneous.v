(** Federer (1969), 2.7.2, printed p. 122: "Two important special cases
    occur when X = G and the multiplication of G is used to define either
    (1) A(g,x) = gx, or (2) A(g,x) = xg^{-1} whenever g in G and x in G."
    Calling these "special cases" of 2.7.1 presupposes that G is a
    homogeneous space of itself through either action; this is proved here
    for every topological group, from the group laws, the continuity of the
    multiplication and of the inversion, and the fact that translations and
    inversion are homeomorphisms. The orbit map of (1) at x is right
    multiplication by x, that of (2) at x is g |-> xg^{-1}. Local
    compactness and the Hausdorff property of G are not used. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import TopologicalProductMaps HomeomorphismUP TopologicalGroupUP
  TopologicalGroupLaws HomogeneousSpaceUP HaarIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Section GroupMultiplicationHomogeneous.
Variable G : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G).
Hypothesis hT : is_topological_group mul inv e.
(** Source for [hG]: the group laws of G, Federer 2.7.1, p. 121, used
    in this section. *)
Let hG := topological_group_laws hT.

(** Source for [left_multiplication_translation]: "In case (1), A_g
    is left multiplication by g", Federer 2.7.2, p. 122. Direct
    formalisation. *)
Lemma left_multiplication_translation g : left_multiplication_action mul g = mul g.
Proof. by []. Qed.

(** Source for [right_multiplication_translation]: "In case (2), A_g
    is right multiplication by g^{-1}", Federer 2.7.2, p. 122. Direct
    formalisation. *)
Lemma right_multiplication_translation g :
  right_multiplication_action mul inv g = fun x => mul x (inv g).
Proof. by []. Qed.

(** Source for [left_multiplication_homogeneous]: Federer 2.7.2,
    p. 122, case (1), A(g,x) = gx, as a special case of 2.7.1, p. 121:
    G is a homogeneous space of G through this action. The action is
    the multiplication, compatibility is associativity, the orbit map
    at x is right multiplication by x, which is open, and gx = y for
    g = yx^{-1}. Supporting lemma for 2.7.2. *)
Theorem left_multiplication_homogeneous : is_homogeneous_space mul (left_multiplication_action mul).
Proof.
constructor.
- exact: topological_group_mul_continuous hT.
- by move=> g h x; rewrite /left_multiplication_action (group_mulA hG).
- by move=> x; exact: right_translation_open_map hT x.
- move=> x; apply/seteqP; split=> // y _.
  by exists (mul y (inv x))=> //; rewrite /orbit_map /left_multiplication_action (group_mulgKV hG).
Qed.

(** Source for [right_multiplication_action_continuous]: continuity
    of (g,x) |-> xg^{-1} on G x G, the first condition of 2.7.1, p. 121,
    for the action 2.7.2(2), p. 122. The map is the multiplication
    composed with (g,x) |-> (x,g^{-1}). *)
Lemma right_multiplication_action_continuous :
  continuous (fun p : G * G => right_multiplication_action mul inv p.1 p.2).
Proof.
have hi : continuous inv := topological_group_inv_continuous hT.
have hq : continuous (fun p : G * G => (p.2, inv p.1)).
  apply: topological_pair_continuous; first exact: second_projection_continuous.
  by move=> p; exact: continuous_comp (@first_projection_continuous G G p) (@hi p.1).
have hm : continuous (fun p : G * G => mul p.1 p.2) := topological_group_mul_continuous hT.
by move=> p; have := continuous_comp (hq p) (@hm (p.2, inv p.1)); exact.
Qed.

(** Source for [right_multiplication_orbit_open]: openness of the
    orbit map g |-> xg^{-1}, the third condition of 2.7.1, p. 121, for
    the action 2.7.2(2), p. 122: it is the inversion followed by left
    multiplication by x, and both are open maps. *)
Lemma right_multiplication_orbit_open x :
  is_open_map (orbit_map (right_multiplication_action mul inv) x).
Proof.
move=> U hU.
have -> : orbit_map (right_multiplication_action mul inv) x @` U = mul x @` (inv @` U).
  apply/seteqP; split=> y.
  - by case=> g hg <-; exists (inv g)=> //; exists g.
  - by case=> _ [g hg <-] <-; exists g.
apply: left_translation_open_map hT x _ _.
exact: homeomorphism_with_inverse_open_map (inversion_homeomorphism hT) U hU.
Qed.

(** Source for [right_multiplication_homogeneous]: Federer 2.7.2,
    p. 122, case (2), A(g,x) = xg^{-1}, as a special case of 2.7.1,
    p. 121: G is a homogeneous space of G through this action. The
    compatibility x(gh)^{-1} = (xh^{-1})g^{-1} uses
    (gh)^{-1} = h^{-1}g^{-1}, and xg^{-1} = y for g = y^{-1}x.
    Supporting lemma for 2.7.2. *)
Theorem right_multiplication_homogeneous :
  is_homogeneous_space mul (right_multiplication_action mul inv).
Proof.
constructor.
- exact: right_multiplication_action_continuous.
- move=> g h x; rewrite /right_multiplication_action (group_invM hG).
  by rewrite (group_mulA hG).
- exact: right_multiplication_orbit_open.
- move=> x; apply/seteqP; split=> // y _.
  exists (mul (inv y) x)=> //.
  by rewrite /orbit_map /right_multiplication_action (group_invM hG) (group_invK hG) (group_mulKVg hG).
Qed.

End GroupMultiplicationHomogeneous.
