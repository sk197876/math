(** Federer (1969), 2.7.5, printed p. 125, proof of the corollary: "Taking B
    as the family of sets {(x,y): x^{-1} y in V} corresponding to all
    neighborhoods V of e, one sees that the action 2.7.2(1) of G on G is
    uniform. Similarly one treats the action 2.7.2(2) by using the sets
    {(x,y): x y^{-1} in V}." Both cases are instances of one argument for a
    map d: G x G -> G, d(x,y) = x^{-1} y in the first case and d(x,y) = x
    y^{-1} in the second, with d(x,x) = e, d(x,z) = d(x,y) d(y,z), d(y,x) =
    d(x,y)^{-1}, y |-> d(x,y) continuous with a continuous left inverse z
    |-> k(x,z) satisfying k(x,e) = x (k(x,z) = xz, respectively z^{-1}x),
    and d(gx,gy) = d(x,y) for the action. The sets {(x,y): d(x,y) in V}
    generate a uniformity: the filter laws hold because V cap V' is a
    neighbourhood of e, inversion of relations corresponds to V |-> V^{-1},
    and if W W subset V, which is possible by the continuity of the
    multiplication at (e,e), the composition of the set for W with itself
    lies in the set for V. Its sections {y: d(x,y) in V} are the inverse
    images of the neighbourhoods V of e under y |-> d(x,y), which maps x to
    e; by the continuity of this map and of its left inverse, the uniformity
    induces the topology of G. The group laws and the continuity of the
    multiplication and of the inversion are used; local compactness and the
    Hausdorff property are not. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import TopologicalGroupUP TopologicalGroupLaws UniformActionUP HaarIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope relation_scope.

Section DivisionUniformity.
Variable G : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G).
Hypothesis hT : is_topological_group mul inv e.
(** Source for [hG]: the group laws of G, Federer 2.7.1, p. 121, used
    in this section. *)
Let hG := topological_group_laws hT.
Variables (d k : G -> G -> G).
Hypothesis hdd : forall x, d x x = e.
Hypothesis hdm : forall x y z, d x z = mul (d x y) (d y z).
Hypothesis hdi : forall x y, d y x = inv (d x y).
Hypothesis hdc : forall x, continuous (d x).
Hypothesis hkc : forall x, continuous (k x).
Hypothesis hkd : forall x y, k x (d x y) = y.
Hypothesis hke : forall x, k x e = x.

(** Source for [division_entourage]: the sets {(x,y): x^{-1} y in V}
    and {(x,y): x y^{-1} in V} of Federer 2.7.5, p. 125, written with
    d(x,y) = x^{-1} y, respectively d(x,y) = x y^{-1}. Definition. *)
Definition division_entourage (V : set G) : set (G * G) := [set p | V (d p.1 p.2)].

(** Source for [division_entourage_family]: "B as the family of sets
    {(x,y): x^{-1} y in V} corresponding to all neighborhoods V of e",
    Federer 2.7.5, p. 125, and the family of the sets
    {(x,y): x y^{-1} in V}. Definition. *)
Definition division_entourage_family : set_system (G * G) :=
  [set division_entourage V | V in nbhs e].

(** Source for [division_uniformity]: the uniformity with basis B in
    Federer 2.7.5, p. 125: the sets containing some member of B.
    Definition. *)
Definition division_uniformity : set_system (G * G) := filter_from (nbhs e) division_entourage.

(** Source for [division_uniformity_laws]: the family of Federer 2.7.5,
    p. 125, is the basis of a uniformity: the entourage laws of 2.7.3,
    p. 123, hold for the sets containing some
    {(x,y): d(x,y) in V}. Supporting theorem. *)
Lemma division_uniformity_laws : is_uniformity division_uniformity.
Proof.
have hic : continuous inv := topological_group_inv_continuous hT.
have hinv : inv @ e --> e by have := hic e; rewrite /continuous_at (group_inv1 hG).
constructor.
- apply: filter_from_filter; first by exists setT; exact: filterT.
  move=> V1 V2 h1 h2; exists (V1 `&` V2); first exact: filterI.
  by move=> p hp; split; case: hp.
- move=> D [V hV hVD] [x y] /diagonalP <-; apply: hVD.
  by rewrite /division_entourage /= hdd; exact: nbhs_singleton hV.
- move=> D [V hV hVD]; exists (inv @^-1` V); first exact: hinv.
  by move=> [x y] hxy; apply: hVD; rewrite /division_entourage /= hdi.
- move=> D [V hV hVD].
  have hmc : continuous (fun p : G * G => mul p.1 p.2) := topological_group_mul_continuous hT.
  have hm := hmc (e, e).
  rewrite /continuous_at /= (group_mul1g hG) in hm.
  have [[W1 W2] /= [hW1 hW2] hW12] := hm _ hV.
  exists (division_entourage (W1 `&` W2)); first by exists (W1 `&` W2)=> //; exact: filterI.
  move=> [x z] [y [h1 _] [_ h2]]; apply: hVD; rewrite /division_entourage /= (hdm x y z).
  exact: (hW12 (d x y, d y z)).
Qed.

(** Source for [division_uniformity_topology]: the uniformity of
    Federer 2.7.5, p. 125, induces the topology of G: the section
    {y: d(x,y) in V} is the inverse image of V under the continuous map
    y |-> d(x,y), which maps x to e and has the continuous left inverse
    z |-> k(x,z). Supporting theorem. *)
Lemma division_uniformity_topology : uniformity_induces_topology division_uniformity.
Proof.
move=> x; apply/seteqP; split=> N hN.
  have hk := @hkc x e; rewrite /continuous_at hke in hk.
  exists (division_entourage (k x @^-1` N)); first by exists (k x @^-1` N)=> //; exact: hk.
  by move=> y /xsectionP; rewrite /division_entourage /= hkd.
case: hN=> D [V hV hVD] hDN.
have hd := @hdc x x; rewrite /continuous_at hdd in hd.
apply: (@filterS _ _ _ (d x @^-1` V)); last exact: hd _ hV.
by move=> y hy; apply: hDN; apply/xsectionP; exact: hVD.
Qed.

(** Source for [division_uniformity_basis]: B is a basis of the
    uniformity, Federer 2.7.5, p. 125. Supporting theorem. *)
Lemma division_uniformity_basis : is_uniformity_basis division_uniformity division_entourage_family.
Proof.
split; first by move=> _ [V hV <-]; exists V.
by move=> D [V hV hVD]; exists (division_entourage V)=> //; exists V.
Qed.

(** Source for [division_entourage_invariant]: B is G invariant in the
    sense of Federer 2.7.3, p. 123, when d(gx,gy) = d(x,y); for
    2.7.5, p. 125, (gx)^{-1}(gy) = x^{-1} y and
    (xg^{-1})(yg^{-1})^{-1} = x y^{-1}. Supporting theorem. *)
Lemma division_entourage_invariant (A : G -> G -> G) :
  (forall g x y, d (A g x) (A g y) = d x y) -> is_invariant_entourage_family A division_entourage_family.
Proof. by move=> hAd _ g x y [V hV <-]; rewrite /division_entourage /= hAd. Qed.

(** Source for [division_acts_uniformly]: "one sees that the action
    ... of G on G is uniform", Federer 2.7.5, p. 125, for an action
    preserving d. Supporting theorem. *)
Theorem division_acts_uniformly (A : G -> G -> G) :
  (forall g x y, d (A g x) (A g y) = d x y) -> acts_uniformly A.
Proof.
move=> hAd; exists division_uniformity, division_entourage_family; split.
- exact: division_uniformity_laws.
- exact: division_uniformity_topology.
- exact: division_uniformity_basis.
- exact: division_entourage_invariant.
Qed.

End DivisionUniformity.

Section GroupUniformity.
Variable G : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G).
Hypothesis hT : is_topological_group mul inv e.
(** Source for [hG]: the group laws of G, Federer 2.7.1, p. 121, used
    in this section. *)
Let hG := topological_group_laws hT.

(** Source for [left_division_entourage_basis]: "Taking B as the
    family of sets {(x,y): x^{-1} y in V} corresponding to all
    neighborhoods V of e, one sees that the action 2.7.2(1) of G on G is
    uniform", Federer 2.7.5, p. 125. Direct formalisation: the sets
    containing a member of B form a uniformity which induces the
    topology of G, and B is a G invariant basis of it. *)
Theorem left_division_entourage_basis :
  let d := fun x y => mul (inv x) y in
  [/\ is_uniformity (division_uniformity e d),
    uniformity_induces_topology (division_uniformity e d),
    is_uniformity_basis (division_uniformity e d) (division_entourage_family e d) &
    is_invariant_entourage_family (left_multiplication_action mul) (division_entourage_family e d)].
Proof.
move=> d.
have hdd x : d x x = e := group_mulVg hG x.
have hdm x y z : d x z = mul (d x y) (d y z).
  by rewrite /d -(group_mulA hG) (group_mulKVg hG).
have hdi x y : d y x = inv (d x y) by rewrite /d (group_invM hG) (group_invK hG).
have hdc x : continuous (d x) := left_translation_continuous hT (inv x).
have hkc x : continuous (mul x) := left_translation_continuous hT x.
have hkd x y : mul x (d x y) = y := group_mulKVg hG x y.
have hke x : mul x e = x := group_mulg1 hG x.
have h1 := division_uniformity_laws hT hdd hdm hdi.
have h2 := @division_uniformity_topology G e d mul hdd hdc hkc hkd hke.
split=> //.
- exact: division_uniformity_basis.
- apply: division_entourage_invariant=> g x y.
  by rewrite /d /left_multiplication_action (group_invM hG) -(group_mulA hG) (group_mulKg hG).
Qed.

(** Source for [right_division_entourage_basis]: "Similarly one treats
    the action 2.7.2(2) by using the sets {(x,y): x y^{-1} in V}",
    Federer 2.7.5, p. 125. Direct formalisation. *)
Theorem right_division_entourage_basis :
  let d := fun x y => mul x (inv y) in
  [/\ is_uniformity (division_uniformity e d),
    uniformity_induces_topology (division_uniformity e d),
    is_uniformity_basis (division_uniformity e d) (division_entourage_family e d) &
    is_invariant_entourage_family (right_multiplication_action mul inv) (division_entourage_family e d)].
Proof.
move=> d.
have hdd x : d x x = e := group_mulgV hG x.
have hdm x y z : d x z = mul (d x y) (d y z).
  by rewrite /d -(group_mulA hG) (group_mulKg hG).
have hdi x y : d y x = inv (d x y) by rewrite /d (group_invM hG) (group_invK hG).
have hdc x : continuous (d x).
  have hic : continuous inv := topological_group_inv_continuous hT.
  have hlc : continuous (mul x) := left_translation_continuous hT x.
  move=> y; apply: continuous_comp; first exact: hic.
  exact: (hlc (inv y)).
pose k := fun x z => mul (inv z) x.
have hkc x : continuous (k x).
  have hic : continuous inv := topological_group_inv_continuous hT.
  have hrc : continuous (fun h => mul h x) := right_translation_continuous hT x.
  move=> z; exact: (@continuous_comp G G G inv (fun h => mul h x) z (hic z) (hrc (inv z))).
have hkd x y : k x (d x y) = y.
  by rewrite /k /d (group_invM hG) (group_invK hG) (group_mulgKV hG).
have hke x : k x e = x by rewrite /k (group_inv1 hG) (group_mul1g hG).
have h1 := division_uniformity_laws hT hdd hdm hdi.
have h2 := @division_uniformity_topology G e d k hdd hdc hkc hkd hke.
split=> //.
- exact: division_uniformity_basis.
- apply: division_entourage_invariant=> g x y.
  rewrite /d /right_multiplication_action (group_invM hG) (group_invK hG).
  by rewrite -(group_mulA hG) (group_mulKg hG).
Qed.

(** Source for [left_multiplication_acts_uniformly]: "the action
    2.7.2(1) of G on G is uniform", Federer 2.7.5, p. 125. Direct
    formalisation. *)
Theorem left_multiplication_acts_uniformly : acts_uniformly (left_multiplication_action mul).
Proof.
have [hE hnb hB hinv] := left_division_entourage_basis.
by do 2 eexists; split; [exact: hE|exact: hnb|exact: hB|exact: hinv].
Qed.

(** Source for [right_multiplication_acts_uniformly]: "Similarly one
    treats the action 2.7.2(2)", Federer 2.7.5, p. 125: the action
    A(g,x) = x g^{-1} of G on G is uniform. Direct formalisation. *)
Theorem right_multiplication_acts_uniformly : acts_uniformly (right_multiplication_action mul inv).
Proof.
have [hE hnb hB hinv] := right_division_entourage_basis.
by do 2 eexists; split; [exact: hE|exact: hnb|exact: hB|exact: hinv].
Qed.

End GroupUniformity.
