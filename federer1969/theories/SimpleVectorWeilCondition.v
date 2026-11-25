(** Federer (1969), 2.7.16, example (4), printed p. 138: "However, the
    action of GL(n, R) on the space of all nonzero simple m vectors of R^n
    admits a |det|^{-m} covariant integral. In fact, if W is the m
    dimensional subspace associated with a nonzero simple m vector x, the
    isotropy group at x consists of all those endomorphisms g of R^n for
    which g(W) = W and det(g|W) = 1, hence is a normal subgroup of the group
    studied in (3), and it follows from 2.7.12 that the modular function of
    the present isotropy group equals |det|^m." Here V is a space with an
    inner product and a finite basis, the space X of nonzero simple
    m-vectors is the homogeneous space of SimpleVectorHomogeneous.v (for 0 <
    m <= n), and W is the associated subspace FedererSimple.T of 1.6.1, p.
    23. If (wedge_m g) xi = xi and v in W, then xi wedge g(v) = wedge g (xi
    wedge v) = 0, so g(W) c W; for g with g(W) = W and a basis w of W with
    xi = w_1 wedge ... wedge w_m, (wedge_m g) xi = det(g|W) xi
    (exterior_Leibniz and the permutation formula of 1.3.4, p. 16). The set
    N of the members h of the group H of example (3) with det(h|W) = 1 is a
    closed normal subgroup of H, isomorphic to the isotropy group as a
    topological group; by 2.7.12, p. 129, Delta_N = Delta_H|N, and
    Delta_H(h) = |det(h|W)|^{-n} |det h|^m = |det h|^m on N. Weil's
    condition 2.7.11(1), p. 128, for chi = |det|^{-m} and Delta_{GL(n, R)} =
    1 holds, and its sufficiency gives the covariant integral. The local
    erratum has no entry for this passage. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From mathcomp Require Import fingroup perm.
From Federer Require Import RealMetricBackground InnerProductUP InnerMetric LinearBasis Bilinear TensorUP Hom
  HomInner FiniteDualDimension Annihilator ModuleQuotient SubspaceCarrier GrassmannSubspaces AlgebraUP
  GradedComponents ExteriorGrading ExteriorAlgebra ExteriorMaps FiniteExteriorPowers ExteriorDeterminant
  ExteriorLeibniz InversionCount InnerExterior InnerExteriorPositivity AssociatedSubspace SimpleElementary
  SimpleDimensionCriterion EuclideanLinearMaps EuclideanInnerProduct FiniteCoordinates GrassmannAbbreviations
  OrthonormalFamilies GramSchmidt OrthonormalisationUP CompactSupportFunctionUP DaniellIntegralUP IsotropyGroupTopology TopologicalProductMaps
  TopologicalGroupUP TopologicalGroupLaws HomeomorphismUP HomogeneousSpaceUP HomogeneousSpaceLaws
  CovariantIntegralUP HaarIntegralUP ModularFunctionUP ModularFunction NormalSubgroupUP
  CosetSpaceInvariantIntegrals WeilCondition HomSpaceTopology LinearGroupTopology LinearGroupSealed
  HomHaarCovariance LinearGroupUnimodular OrthogonalGroupTopology SubspaceStabiliser
  StabiliserModularFunction GroupIsomorphismModular SimpleVectorAction SimpleVectorFrames
  SimpleVectorHomogeneous.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section SimpleIsotropy.
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
Local Notation X := (set_type (nonzero_simple_set hB m)).
Local Notation gw := (exterior_group_map hB hb m).
Local Notation A := (simple_vector_action hB hb m).
Local Notation det := (linear_group_det hB hb).

Variable x : X.
Local Notation W := (FedererSimple.T (set_val x : exterior_power V m)).
Local Notation Stab := (set_type (subspace_stabiliser hB hb W)).

(** Source for [simple_associated_grassmann]: the subspace associated
    with a nonzero simple m-vector is m dimensional, Federer 1.6.1,
    p. 24, "the m dimensional subspace associated with a nonzero simple
    m vector x", 2.7.16, p. 138. Supporting lemma. *)
Lemma simple_associated_grassmann : grassmann_pred m W.
Proof.
have [hx0 hxs] := set_valP x.
have [e [he _]] := simple_is_basis_product h2 hx0 hxs.
by exists e.
Qed.

Local Notation hW := simple_associated_grassmann.

(** Source for [simple_isotropy_stabiliser]: if (wedge_m g) x = x, then
    g(W) = W, Federer 2.7.16, p. 138: for v in W,
    x wedge g(v) = (wedge g)(x wedge v) = 0 (1.3.1, p. 13, and 1.6.1,
    p. 23). Supporting lemma. *)
Lemma simple_isotropy_stabiliser (g : GL) : A g x = x -> subspace_stabiliser hB hb W g.
Proof.
move=> hg; apply/(subspace_stabiliser_iff hW)=> v hv.
have hxi : gw g (set_val x) = set_val x := congr1 set_val hg.
pose f := hom_as_linear (set_val g : Hom V V).
change (wedge (component_val (set_val x)) (exterior_generator ((set_val g : Hom V V) v)) = 0).
have e1 : component_val (set_val x) = exterior_algebra_map f (component_val (set_val x)).
  by rewrite -{1}hxi /gw /exterior_group_map component_mapE.
have e2 : exterior_generator ((set_val g : Hom V V) v) = exterior_algebra_map f (exterior_generator v).
  exact: esym (exterior_algebra_mapE f v).
rewrite e1 e2 /wedge -(algebra_map_mul (exterior_algebra_map f)).
have hv' : wedge (component_val (set_val x)) (exterior_generator v) = 0 := hv.
by rewrite /wedge in hv'; rewrite hv' linear0.
Qed.

(** Source for [simple_stabiliser_word]: (wedge_m g) x = det(g|W) x for
    g in the group H of example (3), Federer 2.7.16, p. 138, with
    x = w_1 wedge ... wedge w_m for a basis w of W (1.6.1, p. 24) and
    the permutation formula of 1.3.4, p. 16. Supporting lemma. *)
Lemma simple_stabiliser_word (s : Stab) :
  gw (set_val s) (set_val x) = stabiliser_restriction_det hW s *: (set_val x : exterior_power V m).
Proof.
have [hx0 hxs] := set_valP x.
have [e [he hxe0]] := simple_is_basis_product h2 hx0 hxs.
have hxe : (set_val x : exterior_power V m) = e_lambda (fun i => subspace_val (e i)) (ord_tuple m) := hxe0.
pose a := fun i j => (dual_basis he j (stabiliser_restriction s (e i)) : R).
have hexp i : (set_val (set_val s) : Hom V V) (subspace_val (e i)) = \sum_(j < m) a i j *: subspace_val (e j).
  rewrite -[LHS](stabiliser_restrictionE s (e i)).
  rewrite {1}(basis_vector_expansion he (stabiliser_restriction s (e i))) linear_sum.
  by apply: eq_bigr=> j _; rewrite linearZ.
have hdet : stabiliser_restriction_det hW s =
    \sum_(sg : 'S_m) FedererPermutation.index R sg * \prod_(i < m) a i (sg i).
  rewrite (stabiliser_restriction_detE hW he s).
  apply: (det_formula h2 he (f := stabiliser_restriction s) (b := a))=> i.
  exact: basis_vector_expansion.
have h1 : gw (set_val s) (set_val x) = gw (set_val s) (e_lambda (fun i => subspace_val (e i)) (ord_tuple m)).
  exact: (congr1 (gw (set_val s)) hxe).
have h2' : gw (set_val s) (e_lambda (fun i => subspace_val (e i)) (ord_tuple m)) =
    stabiliser_restriction_det hW s *: e_lambda (fun i => subspace_val (e i)) (ord_tuple m).
  rewrite exterior_group_map_word /word_image.
  have -> : (fun i => (set_val (set_val s) : Hom V V) (subspace_val (e i))) =
      (fun i => \sum_(j < m) a i j *: subspace_val (e j)) by apply: funext=> i; exact: hexp.
  by rewrite word_change_basis -hdet.
have h3 : stabiliser_restriction_det hW s *: e_lambda (fun i => subspace_val (e i)) (ord_tuple m) =
    stabiliser_restriction_det hW s *: (set_val x : exterior_power V m).
  exact: (congr1 (fun y => stabiliser_restriction_det hW s *: y) (esym hxe)).
exact: (etrans h1 (etrans h2' h3)).
Qed.

(** Source for [simple_isotropy_det]: for g in H, (wedge_m g) x = x if
    and only if det(g|W) = 1, Federer 2.7.16, p. 138. Supporting
    lemma. *)
Lemma simple_isotropy_det (s : Stab) : A (set_val s) x = x <-> stabiliser_restriction_det hW s = 1.
Proof.
have hx0 : (set_val x : exterior_power V m) != 0 := (set_valP x).1.
split.
- move=> h; have h' : gw (set_val s) (set_val x) = set_val x := congr1 set_val h.
  rewrite simple_stabiliser_word in h'.
  have : (stabiliser_restriction_det hW s - 1) *: (set_val x : exterior_power V m) = 0.
    by rewrite scalerBl h' scale1r subrr.
  by move/eqP; rewrite scaler_eq0 (negbTE hx0) orbF subr_eq0=> /eqP.
- move=> h; apply: val_inj.
  change (gw (set_val s) (set_val x) = set_val x).
  by rewrite simple_stabiliser_word h scale1r.
Qed.

(** Source for [simple_isotropy_characterisation]: "the isotropy group
    at x consists of all those endomorphisms g of R^n for which
    g(W) = W and det(g|W) = 1", Federer 2.7.16, p. 138. Direct
    formalisation: g fixes x if and only if g belongs to H and its
    restriction to W has determinant 1. *)
Theorem simple_isotropy_characterisation (g : GL) :
  A g x = x <-> exists2 hg : subspace_stabiliser hB hb W g,
    stabiliser_restriction_det hW (exist _ g (mem_set hg) : Stab) = 1 & True.
Proof.
split.
- move=> h; have hg := simple_isotropy_stabiliser h.
  exists hg=> //; exact: (simple_isotropy_det (exist _ g (mem_set hg))).1 h.
- move=> [hg hd _]; exact: (simple_isotropy_det (exist _ g (mem_set hg))).2 hd.
Qed.

Variables (mulS : Stab -> Stab -> Stab) (invS : Stab -> Stab) (eS : Stab).
Hypothesis hS : is_subgroup_restriction mul inv unit (subspace_stabiliser hB hb W) mulS invS eS.

(** Source for [simple_det_kernel]: the members h of H with
    det(h|W) = 1, Federer 2.7.16, p. 138. Definition. *)
Definition simple_det_kernel : set Stab := [set s | stabiliser_restriction_det hW s = 1].

(** Source for [simple_det_kernel_normal]: "hence is a normal subgroup
    of the group studied in (3)", Federer 2.7.16, p. 138: the kernel of
    the homomorphism h |-> det(h|W). Direct formalisation. *)
Theorem simple_det_kernel_normal : is_normal_subgroup mulS invS eS simple_det_kernel.
Proof.
have hnz := @stabiliser_restriction_det_nonzero R V B hB n b hb W m hW.
split; first split.
- exact: (stabiliser_restriction_det_unit hW hS).
- move=> s t hs ht; rewrite /simple_det_kernel /= (stabiliser_restriction_det_mul hW hS).
  by rewrite hs ht mulr1.
- move=> s hs; rewrite /simple_det_kernel /= (stabiliser_restriction_det_inv hW hS).
  by rewrite hs invr1.
- move=> g s hs; rewrite /simple_det_kernel /= !(stabiliser_restriction_det_mul hW hS).
  by rewrite (stabiliser_restriction_det_inv hW hS) hs mulr1 mulfV.
Qed.

(** Source for [simple_det_kernel_closed]: the kernel of the continuous
    homomorphism h |-> det(h|W) is closed in H, Federer 2.7.16, p. 138.
    Supporting lemma. *)
Lemma simple_det_kernel_closed : closed simple_det_kernel.
Proof.
have hc : continuous (fun s : Stab => (stabiliser_restriction_det hW s : R^o)).
  exact: (@stabiliser_restriction_det_continuous R V B hB n b hb W m hW).
have -> : simple_det_kernel = (fun s : Stab => (stabiliser_restriction_det hW s : R^o)) @^-1` [set 1] by [].
by apply: preimage_closed; [move=> s _; exact: hc|exact: closed_eq].
Qed.

Local Notation I := (isotropy_subgroup A x).
Local Notation NS := (set_type simple_det_kernel).

(** Source for [isotropy_to_kernel]: the identification of the isotropy
    group at x with the subgroup N of H, Federer 2.7.16, p. 138.
    Definition. *)
Definition isotropy_to_kernel (t : I) : NS.
Proof.
pose s : Stab := exist _ (set_val t) (mem_set (simple_isotropy_stabiliser (set_valP t))).
apply: (exist _ s); apply: mem_set.
exact: ((simple_isotropy_det s).1 (set_valP t)).
Defined.

(** Source for [kernel_to_isotropy]: the inverse identification,
    Federer 2.7.16, p. 138. Definition. *)
Definition kernel_to_isotropy (s : NS) : I :=
  exist _ (set_val (set_val s)) (mem_set ((simple_isotropy_det (set_val s)).2 (set_valP s))).

(** Source for [isotropy_kernel_homeomorphism]: the isotropy group at x
    and N are homeomorphic, Federer 2.7.16, p. 138, both carrying the
    relative topology of GL(n, R). Supporting lemma. *)
Lemma isotropy_kernel_homeomorphism : is_homeomorphism_with_inverse isotropy_to_kernel kernel_to_isotropy.
Proof.
split.
- apply: set_type_continuous_into; apply: set_type_continuous_into.
  exact: set_type_val_continuous.
- apply: set_type_continuous_into=> s.
  apply: (@continuous_comp NS Stab GL set_val set_val); exact: set_type_val_continuous.
- by move=> t; apply: val_inj.
- by move=> s; apply: val_inj; apply: val_inj.
Qed.

Section IsotropyStructure.
Variables (mulI : I -> I -> I) (invI : I -> I) (eI : I).
Hypothesis hRI : is_subgroup_restriction mul inv unit I mulI invI eI.
Variables (mulN : NS -> NS -> NS) (invN : NS -> NS) (eN : NS).
Hypothesis hRN : is_subgroup_restriction mulS invS eS simple_det_kernel mulN invN eN.

(** Source for [isotropy_to_kernel_mul]: the identification is a
    homomorphism, Federer 2.7.16, p. 138. Supporting lemma. *)
Lemma isotropy_to_kernel_mul (t t' : I) :
  isotropy_to_kernel (mulI t t') = mulN (isotropy_to_kernel t) (isotropy_to_kernel t').
Proof.
apply: val_inj; apply: val_inj.
rewrite /= -!set_valE (subgroup_restriction_mul hRN) (subgroup_restriction_mul hS) (subgroup_restriction_mul hRI).
by [].
Qed.

End IsotropyStructure.

(** Source for [simple_isotropy_modular]: "it follows from 2.7.12 that
    the modular function of the present isotropy group equals |det|^m",
    Federer 2.7.16, p. 138, for any restricted structure and modular
    function of the isotropy group at x. Direct formalisation: the
    isotropy group is isomorphic to the closed normal subgroup N of H,
    Delta_N = Delta_H|N by 2.7.12, p. 129, and Delta_H(h) =
    |det(h|W)|^{-n} |det h|^m with det(h|W) = 1 on N (example (3)). *)
Theorem simple_isotropy_modular (mulI : I -> I -> I) (invI : I -> I) (eI : I) (DI : I -> R) :
  is_subgroup_restriction mul inv unit I mulI invI eI -> is_modular_function mulI invI DI ->
  forall t : I, DI t = `|det (set_val t)| ^+ m.
Proof.
move=> hRI hDI t.
have hGl := linear_group_operations_lch hB hb.
have hSl := subspace_stabiliser_lch hW hS.
have hXH : hausdorff_space X by exact: simple_vector_space_hausdorff.
have hIc : closed I.
  have hx1 : closed [set x] by exact: accessible_closed_set1 (hausdorff_accessible hXH) x.
  have -> : I = (fun g : GL => A g x) @^-1` [set x] by [].
  apply: preimage_closed hx1=> g _.
  have hp : continuous (fun g : GL => (g, x)).
    by apply: topological_pair_continuous; [move=> ?|exact: cst_continuous].
  have hAc := @simple_vector_action_continuous R V B hB n b hb m.
  exact: (continuous_comp (hp g) (hAc (g, x))).
have hIl : is_locally_compact_hausdorff_group mulI invI eI.
  exact: (subgroup_restriction_locally_compact_hausdorff hRI hGl hIc).
have hN := simple_det_kernel_normal.
have [mulN [invN [eN hRN]]] := subgroup_restriction_exists (normal_subgroup_subgroup hN).
have hNl : is_locally_compact_hausdorff_group mulN invN eN.
  exact: (subgroup_restriction_locally_compact_hausdorff hRN hSl simple_det_kernel_closed).
have [DN hDN] := modular_function_exists R hNl.
have [DH hDH] := modular_function_exists R hSl.
rewrite (isomorphism_modular_function hIl hNl isotropy_kernel_homeomorphism
  (isotropy_to_kernel_mul hRI hRN) hDI hDN t).
rewrite (normal_subgroup_modular_restriction hSl hN simple_det_kernel_closed hRN hDH hDN).
rewrite (subspace_stabiliser_modular hW hS hDH).
have -> : stabiliser_restriction_det hW (set_val (isotropy_to_kernel t)) = 1 := set_valP (isotropy_to_kernel t).
by rewrite normr1 expr1n invr1 mul1r.
Qed.

End SimpleIsotropy.

Section SimpleCovariant.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Variable m : nat.
Hypothesis hm : (0 < m)%N.
Hypothesis hmn : (m <= n)%N.
Local Notation h2 := (euclidean_two_nonzero R).
Local Notation GL := (set_type (linear_group hB hb)).
Local Notation mul := (linear_group_mul hB hb).
Local Notation inv := (linear_group_inv hB hb).
Local Notation unit := (linear_group_unit hB hb).
Local Notation X := (set_type (nonzero_simple_set hB m)).
Local Notation A := (simple_vector_action hB hb m).
Local Notation det := (linear_group_det hB hb).
Local Notation KX := (@compactly_supported_continuous_functions R X).

(** Source for [simple_vector_covariant_integral]: "the action of
    GL(n, R) on the space of all nonzero simple m vectors of R^n admits
    a |det|^{-m} covariant integral", Federer 2.7.16, p. 138, for
    0 < m <= n: a nonzero |det|^{-m} covariant integral on K(X) exists.
    Direct formalisation, by the sufficiency in 2.7.11(1), p. 128:
    |det t|^{-m} Delta_{G^x}(t) = |det t|^{-m} |det t|^m = 1 =
    Delta_{GL(n, R)}(t). *)
Theorem simple_vector_covariant_integral :
  exists nu : (X -> R) -> R,
    is_covariant_integral A (fun g : GL => `|det g| ^- m) nu /\ exists2 v, KX v & nu v <> 0.
Proof.
have hGl := linear_group_operations_lch hB hb.
have hA := simple_vector_homogeneous hB hb hm hmn.
have [hX hlX] := simple_vector_space_locally_compact hB hb hm hmn.
have [o [ho hgs]] := orthonormal_basis_exists hB hb.
have hoo := orthonormalisation_orthonormal hgs.
pose u := fun i : 'I_m => o (widen_ord hmn i).
have hu : orthonormal_family B u.
  have hinj : injective (widen_ord hmn) by move=> i j /(congr1 val) /= hij; exact: val_inj.
  by move=> i j; rewrite /u hoo (inj_eq hinj).
pose x := frame_point hB hu.
have [mulI [invI [eI [hRI hlI]]]] := isotropy_group_exists x hGl hA hX.
have [DG hDG] := modular_function_exists R hGl.
have [DI hDI] := modular_function_exists R hlI.
have hchiM (g h : GL) : `|det (mul g h)| ^- m = `|det g| ^- m * `|det h| ^- m.
  by rewrite linear_group_det_mul normrM exprMn invfM.
have hchi0 (g : GL) : `|det g| ^- m != 0.
  by rewrite invr_eq0 expf_neq0 // normr_eq0 linear_group_det_nonzero.
have hchic : continuous ((fun g : GL => `|det g| ^- m) : GL -> real_line_metric R).
  exact: linear_group_det_power_continuous.
have [mulS [invS [eS hS]]] := subspace_stabiliser_restriction_exists hB hb
  (FedererSimple.T (set_val x : exterior_power V m)).
apply: (weil_condition_sufficient hGl hA hX hlX hRI hDG hDI hchiM hchi0 hchic)=> t.
rewrite (simple_isotropy_modular hS hRI hDI t) (linear_group_modular_unit hB hb hDG).
rewrite mulVf //; rewrite expf_neq0 // normr_eq0; exact: linear_group_det_nonzero.
Qed.

End SimpleCovariant.

Section EuclideanSimpleCovariant.
Variable R : realType.
Variables n m : nat.
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation GL := (set_type (linear_group hBn hbn)).
Local Notation X := (set_type (nonzero_simple_set hBn m)).
Local Notation KX := (@compactly_supported_continuous_functions R X).

(** Source for [euclidean_simple_vector_covariant_integral]: "the
    action of GL(n, R) on the space of all nonzero simple m vectors of
    R^n admits a |det|^{-m} covariant integral", Federer 2.7.16, p. 138,
    for R^n with the inner product of 1.7.1 and 0 < m <= n. Direct
    formalisation of the instance. *)
Corollary euclidean_simple_vector_covariant_integral : (0 < m)%N -> (m <= n)%N ->
  exists nu : (X -> R) -> R,
    is_covariant_integral (simple_vector_action hBn hbn m)
      (fun g : GL => `|linear_group_det hBn hbn g| ^- m) nu /\ exists2 v, KX v & nu v <> 0.
Proof. by move=> hm hmn; exact: simple_vector_covariant_integral. Qed.

End EuclideanSimpleCovariant.
