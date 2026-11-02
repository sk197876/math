(** Federer (1969), 2.7.16, example (5), printed p. 138: "For 0 < m < n,
    there exists no chi covariant integral with respect to the action of G
    on the space X of all m dimensional affine subspaces of R^n. In fact,
    choosing an m dimensional vectorsubspace W of R^n we now find that the
    isotropy group G^W equals M^{-1}(H x W), where H = GL(n, R) cap {h :
    h(W) = W}, and argue as above to prove that the modular function of G^W
    has the value |det[L(g)|W]|^{-1} Delta_H[L(g)] at g. Since H is the
    group studied in (3) [under the name "G"], we can show as in (4) that
    Weil's condition fails in the present case." The absolute value is that
    of the erratum (book p. 138, line 34). Here G is the affine group of V
    (AffineGroupTopology.v) acting on the space X of m dimensional affine
    subspaces (AffineSubspaceAffineAction.v), and the vector subspace W is
    the point tau_0 W of X. Its isotropy group is M^{-1}(H x W)
    (affine_subspace_affine_isotropy), whose modular function is computed in
    AffineStabiliserModular.v; Delta_G is that of the first part of example
    (5) (AffineGroupModular.v) and Delta_H that of example (3). "As in (4)":
    a nonzero chi covariant integral makes chi a continuous homomorphism
    (2.7.1, p. 122); g |-> chi(g, 0) is a homomorphism of GL(n, R), hence
    equal to 1 where det g = 1 (SpecialLinearCommutators.v). For the member
    t of H acting as 2^{n-m} on W and as 2^{-m} on a complement, det t = 1
    and |det(t|W)| = 2^{m(n-m)}; Weil's condition 2.7.11(1), p. 128, at (t,
    0) would give |det(t|W)|^{-1} |det(t|W)|^{-n} = 1. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealMetricBackground InnerProductUP InnerMetric LinearBasis TensorUP Hom HomInner
  ModuleQuotient GrassmannSubspaces CompactSupportFunctionUP DaniellIntegralUP IsotropyGroupTopology
  TopologicalGroupUP TopologicalGroupLaws HomeomorphismUP HomogeneousSpaceUP HomogeneousSpaceLaws
  CovariantIntegralUP CovariantCharacterContinuity HaarIntegralUP ModularFunctionUP ModularFunction
  WeilCondition HomSpaceTopology LinearGroupTopology LinearGroupSealed HomHaarCovariance
  GrassmannHomogeneousSpace EuclideanInnerProduct FiniteCoordinates GrassmannAbbreviations
  AffineGroupTopology AffineSubspaceSpace SubspaceStabiliser StabiliserModularFunction GroupIsomorphismModular
  SpecialLinearCommutators LinearGrassmannAction AffineSubspaceAffineAction AffineGroupModular
  AffineStabiliserModular.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section AffineSubspaceWeil.
Variable R : realType.
Variables U V : lmodType R.
Variables (C : U -> U -> R) (B : V -> V -> R).
Hypotheses (hC : is_inner_product C) (hB : is_inner_product B).
Variables (m : nat) (c : 'I_m -> U) (n : nat) (b : 'I_n -> V).
Hypotheses (hc : is_basis c) (hb : is_basis b).
Local Notation VT := (inner_metric_space hB).
Local Notation GL := (set_type (linear_group hB hb)).
Local Notation AG := (GL * VT)%type.
Local Notation mul := (linear_group_mul hB hb).
Local Notation amul := (affine_group_mul hB hb).
Local Notation ainv := (affine_group_inv hB hb).
Local Notation aunit := (affine_group_unit hB hb).
Local Notation X := (affine_subspace_space hC hB hc hb).
Local Notation A := (affine_subspace_affine_action hC hB hc hb).
Local Notation KX := (@compactly_supported_continuous_functions R X).
Local Notation Stab W := (set_type (subspace_stabiliser hB hb (grassmann_val (W : G V m)))).

(** Source for [hAG]: the affine group is a locally compact Hausdorff
    group, Federer 2.7.16, p. 134, used in this section. *)
Let hAG := affine_group_lch hB hb.
(** Source for [hA]: X is a homogeneous space of the affine group,
    Federer 2.7.16, p. 138, used in this section. *)
Let hA : is_homogeneous_space amul A := affine_subspace_affine_homogeneous hC hB hc hb.
(** Source for [hX]: X is Hausdorff, used in this section. *)
Let hX : hausdorff_space X := (affine_subspace_affine_locally_compact hC hB hc hb).1.
(** Source for [hlX]: X is locally compact, used in this section. *)
Let hlX : locally_compact [set: X] := (affine_subspace_affine_locally_compact hC hB hc hb).2.

(** Source for [affine_isotropy_stabiliser_eq]: "the isotropy group
    G^W equals M^{-1}(H x W)", Federer 2.7.16, p. 138, in the form
    used with equal_subgroups_modular. Supporting lemma. *)
Lemma affine_isotropy_stabiliser_eq (W : G V m) :
  isotropy_subgroup A (affine_subspace_of 0 W : X) = affine_subspace_stabiliser hB hb (grassmann_val W).
Proof. exact: affine_subspace_affine_isotropy. Qed.

(** Source for [affine_isotropy_modular]: "the modular function of G^W
    has the value |det[L(g)|W]|^{-1} Delta_H[L(g)] at g", Federer
    2.7.16, p. 138 (erratum, line 34), for the isotropy group G^W of
    the point W of X with any restricted structure and any modular
    functions of G^W and H. Direct formalisation through
    affine_subspace_stabiliser_modular. *)
Theorem affine_isotropy_modular (W : G V m)
    (mulI invI : _) (eI : isotropy_subgroup A (affine_subspace_of 0 W : X))
    (mulS : Stab W -> Stab W -> Stab W) (invS : Stab W -> Stab W) (eS : Stab W)
    (DI : isotropy_subgroup A (affine_subspace_of 0 W : X) -> R) (DH : Stab W -> R) :
  is_subgroup_restriction amul ainv aunit (isotropy_subgroup A (affine_subspace_of 0 W : X)) mulI invI eI ->
  is_subgroup_restriction mul (linear_group_inv hB hb) (linear_group_unit hB hb)
    (subspace_stabiliser hB hb (grassmann_val W)) mulS invS eS ->
  is_modular_function mulI invI DI -> is_modular_function mulS invS DH ->
  forall s, DI s =
    `|stabiliser_restriction_det (grassmann_proof W)
      (affine_stabiliser_linear (equal_subset_retype (affine_isotropy_stabiliser_eq W) s))|^-1 *
    DH (affine_stabiliser_linear (equal_subset_retype (affine_isotropy_stabiliser_eq W) s)).
Proof.
move=> hRI hS hDI hDH s.
have hcl : closed (isotropy_subgroup A (affine_subspace_of 0 W : X)) := isotropy_subgroup_closed hA hX.
have [mulK [invK [eK hK]]] := affine_subspace_stabiliser_restriction_exists hB hb (grassmann_val W).
have hKl := subgroup_restriction_locally_compact_hausdorff hK hAG
  (affine_subspace_stabiliser_closed (grassmann_proof W)).
have [DK hDK] := modular_function_exists R hKl.
rewrite (equal_subgroups_modular hAG (affine_isotropy_stabiliser_eq W) hcl hRI hK hDI hDK s).
exact: (affine_subspace_stabiliser_modular (grassmann_proof W) hK hS hDK hDH).
Qed.

(** Source for [affine_subspace_no_covariant_integral]: "For 0 < m < n,
    there exists no chi covariant integral with respect to the action
    of G on the space X of all m dimensional affine subspaces of R^n",
    Federer 2.7.16, p. 138, for every function chi, a nonzero chi
    covariant integral forcing chi to be a continuous homomorphism
    (2.7.1, p. 122). Direct formalisation: Weil's condition 2.7.11(1),
    p. 128, fails at (t, 0) for the member t of H with det t = 1 and
    |det(t|W)| = 2^{m(n-m)}, "as in (4)". *)
Theorem affine_subspace_no_covariant_integral (chi : AG -> R) :
  (0 < m)%N -> (m < n)%N ->
  ~ exists nu : (X -> R) -> R, is_covariant_integral A chi nu /\ exists2 v, KX v & nu v <> 0.
Proof.
move=> hm hmn [nu [hnu [v hv hnv]]].
have [hchiM _ hchi0 hchic] := covariant_character_homomorphism (lch_group_topological hAG) hA
  (lch_group_locally_compact hAG) hX hlX hnu (ex_intro _ v (conj hv hnv)).
have [S0 _] := nonzero_integral_point (covariant_integral_daniell hnu) (ex_intro2 _ _ v hv hnv).
pose W : G V m := affine_direction S0.
have [mulI [invI [eI [hRI hlI]]]] := isotropy_group_exists (affine_subspace_of 0 W : X) hAG hA hX.
have [DG hDG] := modular_function_exists R hAG.
have [DI hDI] := modular_function_exists R hlI.
have hw := weil_condition_necessary hAG hA hX hRI hDG hDI hchiM hchi0 hchic hnu (ex_intro2 _ _ v hv hnv).
have [mulS [invS [eS hS]]] := subspace_stabiliser_restriction_exists hB hb (grassmann_val W).
have [DH hDH] := modular_function_exists R (subspace_stabiliser_lch (grassmann_proof W) hS).
have hDHf := subspace_stabiliser_modular (grassmann_proof W) hS hDH.
have hDGf := affine_group_modular hDG.
have h2 : (2 : R) != 0 by rewrite pnatr_eq0.
pose alpha : R := 2 ^+ (n - m).
pose beta : R := (2 ^+ m)^-1.
have ha : alpha != 0 by rewrite expf_neq0.
have hbeta : beta != 0 by rewrite invr_eq0 expf_neq0.
have [t [ht1 ht2]] := stabiliser_scaling_exists hB hb (grassmann_proof W) ha hbeta.
have hdet : stabiliser_det t = 1.
  rewrite ht2 /alpha /beta -!exprM mulnC exprVn -exprM.
  by rewrite mulfV // expf_neq0.
have htI : isotropy_subgroup A (affine_subspace_of 0 W : X) ((set_val t, 0) : AG).
  rewrite (affine_isotropy_stabiliser_eq W); split; first exact: set_valP t.
  exact: subspace_zero.
pose tI : isotropy_subgroup A (affine_subspace_of 0 W : X) := exist _ ((set_val t, 0) : AG) (mem_set htI).
pose chi' := fun g : GL => chi ((g, 0) : AG).
have hchi'M (g h : GL) : chi' (mul g h) = chi' g * chi' h.
  rewrite /chi' -hchiM /affine_group_mul /=.
  by rewrite (linear0 (hom_as_linear (set_val g : Hom V V))) addr0.
have hchi'0 (g : GL) : chi' g != 0 by exact: hchi0.
have hchi1 : chi' (set_val t) = 1 := special_linear_character_unit hchi'M hchi'0 hdet.
have := hw tI.
rewrite (affine_isotropy_modular hRI hS hDI hDH tI) hDGf.
have -> : affine_stabiliser_linear (equal_subset_retype (affine_isotropy_stabiliser_eq W) tI) = t.
  by apply: val_inj.
rewrite hDHf ht1 /=.
change (chi' (set_val t) * (`|alpha ^+ m|^-1 * (`|alpha ^+ m| ^- n * `|stabiliser_det t| ^+ m)) =
  `|stabiliser_det t|^-1 -> False).
rewrite hchi1 hdet normr1 expr1n invr1 mulr1 mul1r -invfM -exprS.
have hgt : 1 < `|alpha ^+ m| ^+ n.+1.
  rewrite normrX ger0_norm ?exprn_ge0 // /alpha -!exprM.
  rewrite exprn_egt1; last by rewrite ltrDl ltr01.
  by rewrite -lt0n !muln_gt0 subn_gt0 hmn hm.
move=> /eqP; rewrite invr_eq1 => /eqP he.
by move: hgt; rewrite he ltxx.
Qed.

End AffineSubspaceWeil.

Section EuclideanAffineSubspaceWeil.
Variable R : realType.
Variables n m : nat.
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation hBm := (@euclidean_inner_productP R m).
Local Notation hbm := (@coordinate_basisP R m).
Local Notation E := (inner_metric_space hBn).
Local Notation GL := (set_type (linear_group hBn hbn)).
Local Notation AG := (GL * E)%type.
Local Notation X := (affine_subspace_space hBm hBn hbm hbn).
Local Notation KX := (@compactly_supported_continuous_functions R X).

(** Source for [euclidean_affine_subspace_no_covariant_integral]: "For
    0 < m < n, there exists no chi covariant integral with respect to
    the action of G on the space X of all m dimensional affine
    subspaces of R^n", Federer 2.7.16, p. 138, for the affine group of
    R^n with the inner product of 1.7.1. Direct formalisation of the
    instance. *)
Corollary euclidean_affine_subspace_no_covariant_integral (chi : AG -> R) :
  (0 < m)%N -> (m < n)%N ->
  ~ exists nu : (X -> R) -> R,
    is_covariant_integral (affine_subspace_affine_action hBm hBn hbm hbn) chi nu /\ exists2 v, KX v & nu v <> 0.
Proof. exact: affine_subspace_no_covariant_integral. Qed.

End EuclideanAffineSubspaceWeil.
