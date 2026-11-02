(** Federer (1969), 2.7.16, example (5), printed p. 138: "To prove this we
    note first that ker L|G = im tau is abelian, hence Delta_G|ker L = 1.
    Then we observe that L^n is |det o L|^{-1} covariant with respect to the
    usual action of G on R^n, with G^0 = GL(n, R), hence |det o L|^{-1} and
    Delta_G agree on GL(n, R)." Two general facts behind these inferences
    are proved here. First, a homeomorphic isomorphism phi of locally
    compact Hausdorff groups carries modular functions to modular functions:
    Delta_H = Delta_S o phi (2.7.8, p. 126), since phi carries left Haar
    integrals of H to left Haar integrals of S (2.5.19, p. 113, and
    EquivariantPushforward.v); this identifies Delta_{G^0} with Delta_{GL(n,
    R)} = 1 in "with G^0 = GL(n, R)". Second, the modular function of a
    locally compact Hausdorff group equals 1 on every closed normal abelian
    subgroup S: Delta_G|S = Delta_S by 2.7.12, p. 129
    (normal_subgroup_modular_restriction), and an abelian group is
    unimodular, because right translation by g is left translation by
    g^{-1}. Federer gives neither argument. The local erratum has no entry
    for this passage of p. 138. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactSupportFunctionUP DaniellIntegralUP
  MonotoneDaniellIntegralUP DaniellSpacePushforward ProperMapUP HomeomorphismUP EquivariantPushforward
  CovariantIntegralUP HaarIntegralUP TopologicalGroupUP TopologicalGroupLaws HaarIntegralExistence
  ModularFunctionUP ModularFunction UnimodularGroupUP UnimodularGroups NormalSubgroupUP
  IsotropyGroupTopology CosetSpaceInvariantIntegrals DaniellIntegralAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section GroupIsomorphism.
Variable R : realType.
Variables H S : topologicalType.
Variables (mulH : H -> H -> H) (invH : H -> H) (eH : H).
Variables (mulS : S -> S -> S) (invS : S -> S) (eS : S).
Hypothesis hH : is_locally_compact_hausdorff_group mulH invH eH.
Hypothesis hS : is_locally_compact_hausdorff_group mulS invS eS.
Variables (phi : H -> S) (psi : S -> H).
Hypothesis hphi : is_homeomorphism_with_inverse phi psi.
Hypothesis hm : forall a c, phi (mulH a c) = mulS (phi a) (phi c).
Local Notation KH := (@compactly_supported_continuous_functions R H).
Local Notation KS := (@compactly_supported_continuous_functions R S).

(** Source for [isomorphism_unit]: a homomorphism carries e to e,
    supporting "with G^0 = GL(n, R)", Federer 2.7.16, p. 138.
    Supporting lemma. *)
Lemma isomorphism_unit : phi eH = eS.
Proof.
have hgH := topological_group_laws (lch_group_topological hH).
have hgS := topological_group_laws (lch_group_topological hS).
have h := hm eH eH; rewrite (group_mul1g hgH) in h.
apply: (@group_mul_left_cancel S mulS invS eS hgS (phi eH)).
by rewrite -h (group_mulg1 hgS).
Qed.

(** Source for [isomorphism_inv]: a homomorphism carries g^{-1} to
    phi(g)^{-1}, supporting Federer 2.7.16, p. 138. Supporting lemma. *)
Lemma isomorphism_inv a : phi (invH a) = invS (phi a).
Proof.
have hgH := topological_group_laws (lch_group_topological hH).
have hgS := topological_group_laws (lch_group_topological hS).
apply: (group_inv_unique hgS).
by rewrite -hm (group_mulgV hgH) isomorphism_unit.
Qed.

(** Source for [isomorphism_left_haar]: phi carries a left Haar
    integral lambda of H to the left Haar integral phi_#(lambda) of S,
    Federer 2.7.2, p. 122, and 2.5.19, p. 113. Supporting lemma: phi is
    a homeomorphism with phi(h x) = phi(h) phi(x), and every s in S is
    phi(psi(s)). *)
Lemma isomorphism_left_haar (lambda : (H -> R) -> R) :
  is_left_haar_integral mulH lambda -> is_left_haar_integral mulS (daniell_pushforward phi lambda).
Proof.
move=> hl.
have hAB : forall g x, phi (left_multiplication_action mulH g x) = (fun h s => mulS (phi h) s) g (phi x).
  by move=> g x; exact: hm.
have [[hd hc] hmono hn] := (@equivariant_nonzero_invariant_integral R H H S (left_multiplication_action mulH)
  (fun h s => mulS (phi h) s) phi psi hphi hAB lambda).1 hl.
split=> //; split=> // u s hu.
have := hc u (psi s) hu.
by rewrite (homeomorphism_right_inverse hphi s).
Qed.

(** Source for [isomorphism_modular_function]: under a homeomorphic
    isomorphism phi of H onto S, Delta_H = Delta_S o phi, Federer
    2.7.8, p. 126, as used for "with G^0 = GL(n, R), hence
    |det o L|^{-1} and Delta_G agree on GL(n, R)", 2.7.16, p. 138.
    Supporting theorem: every left Haar integral lambda of H is right
    Delta_S o phi covariant, because phi_#(lambda) is right Delta_S
    covariant (2.7.8(1)), and 2.7.8 characterises Delta_H by this
    property. *)
Theorem isomorphism_modular_function (DH : H -> R) (DS : S -> R) :
  is_modular_function mulH invH DH -> is_modular_function mulS invS DS -> forall h, DH h = DS (phi h).
Proof.
move=> hDH hDS.
suff -> : DH = DS \o phi by [].
symmetry; apply: (modular_function_unique_left_haar hH hDH)=> lambda hl.
have hr := modular_function_left_haar hDS (isomorphism_left_haar hl).
have hpsi := homeomorphism_with_inverse_symmetric hphi.
split; first exact: (covariant_integral_daniell (nonzero_invariant_integral_invariant hl)).
move=> u h hu.
have hu' : KS (u \o psi).
  exact: (@compactly_supported_compose R S H psi (homeomorphism_continuous hpsi)
    (homeomorphism_with_inverse_proper hpsi) u hu).
have := covariant_integral_law hr (phi h) hu'.
rewrite /daniell_pushforward.
have e1 : ((u \o psi) \o right_multiplication_action mulS invS (phi h)) \o phi =
    u \o right_multiplication_action mulH invH h.
  apply: funext=> x; rewrite /= /right_multiplication_action -isomorphism_inv -hm.
  by rewrite (homeomorphism_left_inverse hphi).
have e2 : (u \o psi) \o phi = u.
  by apply: funext=> x; rewrite /= (homeomorphism_left_inverse hphi).
by rewrite e1 e2.
Qed.

End GroupIsomorphism.

Section CommutativeGroups.
Variable R : realType.
Variable G : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G).
Hypothesis hG : is_locally_compact_hausdorff_group mul inv e.

(** Source for [commutative_group_modular_unit]: the modular function
    of an abelian group is 1, supporting "ker L|G = im tau is abelian,
    hence Delta_G|ker L = 1", Federer 2.7.16, p. 138, with 2.7.8,
    p. 126, and 2.7.12, p. 129. Supporting lemma: for a left Haar
    integral lambda and u in K(G), right translation by g is left
    translation by g^{-1}, so Delta(g) lambda(u) = lambda(u) with
    lambda(u) <> 0. *)
Lemma commutative_group_modular_unit (D : G -> R) :
  (forall g h, mul g h = mul h g) -> is_modular_function mul inv D -> forall g, D g = 1.
Proof.
move=> hc hD g.
have [lambda hl] := left_haar_integral_exists R hG.
have [u hu hu0] := nonzero_invariant_integral_nonzero hl.
have h1 := covariant_integral_law (modular_function_left_haar hD hl) g hu.
have h2 := covariant_integral_law (nonzero_invariant_integral_invariant hl) (inv g) hu.
have e1 : u \o right_multiplication_action mul inv g = u \o left_multiplication_action mul (inv g).
  by apply: funext=> x; rewrite /= /right_multiplication_action /left_multiplication_action hc.
rewrite e1 h2 in h1.
apply: (mulIf (introN eqP hu0)).
by rewrite -h1 mul1r.
Qed.

End CommutativeGroups.

Section AbelianNormal.
Variable R : realType.
Variable G : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G).
Hypothesis hG : is_locally_compact_hausdorff_group mul inv e.

(** Source for [abelian_normal_modular_unit]: "ker L|G = im tau is
    abelian, hence Delta_G|ker L = 1", Federer 2.7.16, p. 138, for a
    closed normal abelian subgroup S of G: Delta_G|S = Delta_S by
    2.7.12, p. 129, and Delta_S = 1 because S is abelian. Supporting
    theorem; Federer gives no argument. *)
Theorem abelian_normal_modular_unit (S : set G) (DG : G -> R) :
  is_normal_subgroup mul inv e S -> closed S -> (forall s t, S s -> S t -> mul s t = mul t s) ->
  is_modular_function mul inv DG -> forall s, S s -> DG s = 1.
Proof.
move=> hN hSc hab hDG s hs.
have [mulS [invS [eS hR]]] := subgroup_restriction_exists (normal_subgroup_subgroup hN).
have hSG := subgroup_restriction_locally_compact_hausdorff hR hG hSc.
have [DS hDS] := modular_function_exists R hSG.
have hres := normal_subgroup_modular_restriction hG hN hSc hR hDG hDS.
have hcomm (a c : S) : mulS a c = mulS c a.
  apply: val_inj; rewrite /= -!set_valE !(subgroup_restriction_mul hR).
  exact: hab (set_valP a) (set_valP c).
pose t : S := exist _ s (mem_set hs).
have -> : s = set_val t by [].
rewrite -hres.
exact: (commutative_group_modular_unit hSG hcomm hDS t).
Qed.

End AbelianNormal.

Section EqualSubgroups.
Variable R : realType.
Variable G : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G).
Hypothesis hG : is_locally_compact_hausdorff_group mul inv e.
Variables S1 S2 : set G.
Hypothesis hE : S1 = S2.
Hypothesis hc : closed S1.
Variables (mul1 : S1 -> S1 -> S1) (inv1 : S1 -> S1) (e1 : S1).
Hypothesis hR1 : is_subgroup_restriction mul inv e S1 mul1 inv1 e1.
Variables (mul2 : S2 -> S2 -> S2) (inv2 : S2 -> S2) (e2 : S2).
Hypothesis hR2 : is_subgroup_restriction mul inv e S2 mul2 inv2 e2.

(** Source for [equal_subset_mem]: a member of S_1 belongs to S_2 when
    S_1 = S_2, supporting "the isotropy group GL(n, R)^W is the group
    studied in (3)", Federer 2.7.16, p. 138. Supporting lemma. *)
Lemma equal_subset_mem (s : S1) : S2 (set_val s).
Proof. rewrite -hE; exact: set_valP. Qed.

(** Source for [equal_subset_mem_inv]: a member of S_2 belongs to S_1,
    Federer 2.7.16, p. 138. Supporting lemma. *)
Lemma equal_subset_mem_inv (s : S2) : S1 (set_val s).
Proof. rewrite hE; exact: set_valP. Qed.

(** Source for [equal_subset_retype]: the identification of S_1 with
    S_2 for S_1 = S_2, Federer 2.7.16, p. 138. Definition. *)
Definition equal_subset_retype (s : S1) : S2 := exist _ (set_val s) (mem_set (equal_subset_mem s)).

(** Source for [equal_subset_retype_inv]: the inverse identification,
    Federer 2.7.16, p. 138. Definition. *)
Definition equal_subset_retype_inv (s : S2) : S1 := exist _ (set_val s) (mem_set (equal_subset_mem_inv s)).

(** Source for [equal_subset_retype_homeomorphism]: the identification
    of S_1 with S_2 is a homeomorphism for the relative topologies,
    Federer 2.7.16, p. 138. Supporting lemma. *)
Lemma equal_subset_retype_homeomorphism : is_homeomorphism_with_inverse equal_subset_retype equal_subset_retype_inv.
Proof.
split.
- by apply: set_type_continuous_into; exact: set_type_val_continuous.
- by apply: set_type_continuous_into; exact: set_type_val_continuous.
- by move=> s; apply: val_inj.
- by move=> s; apply: val_inj.
Qed.

(** Source for [equal_subset_retype_mul]: the identification is a
    homomorphism, Federer 2.7.10, p. 127, for the restricted structures.
    Supporting lemma. *)
Lemma equal_subset_retype_mul (a c : S1) :
  equal_subset_retype (mul1 a c) = mul2 (equal_subset_retype a) (equal_subset_retype c).
Proof.
apply: val_inj; rewrite /= -!set_valE (subgroup_restriction_mul hR1) (subgroup_restriction_mul hR2).
by [].
Qed.

(** Source for [equal_subgroups_modular]: two restricted structures on
    the same closed subgroup have the same modular function, supporting
    "the isotropy group GL(n, R)^W is the group studied in (3)", Federer
    2.7.16, p. 138, with 2.7.8, p. 126. Supporting theorem, by
    isomorphism_modular_function. *)
Theorem equal_subgroups_modular (D1 : S1 -> R) (D2 : S2 -> R) :
  is_modular_function mul1 inv1 D1 -> is_modular_function mul2 inv2 D2 ->
  forall s, D1 s = D2 (equal_subset_retype s).
Proof.
have hl1 := subgroup_restriction_locally_compact_hausdorff hR1 hG hc.
have hc2 : closed S2 by rewrite -hE.
have hl2 := subgroup_restriction_locally_compact_hausdorff hR2 hG hc2.
exact: (isomorphism_modular_function hl1 hl2 equal_subset_retype_homeomorphism equal_subset_retype_mul).
Qed.

End EqualSubgroups.

Section NonzeroIntegralPoint.
Variable R : realType.
Variable X : topologicalType.
Local Notation K := (@compactly_supported_continuous_functions R X).

(** Source for [nonzero_integral_point]: a space carrying an integral
    which does not vanish on K(X) is nonempty, supporting the choice of
    "W in G(n, m)" in Federer 2.7.16, p. 138: otherwise v = 0 and
    nu(v) = 0 by 2.5.5, p. 96. Supporting lemma. *)
Lemma nonzero_integral_point (nu : (X -> R) -> R) :
  is_daniell_integral K nu -> (exists2 v, K v & nu v <> 0) -> exists x : X, True.
Proof.
move=> hnu [v hv hnv].
case: (pselect (exists x : X, True))=> // hX.
exfalso; apply: hnv.
have -> : v = (fun _ => 0) by apply: funext=> x; exfalso; apply: hX; exists x.
exact: (daniell_integral_zero hnu hv).
Qed.

End NonzeroIntegralPoint.
