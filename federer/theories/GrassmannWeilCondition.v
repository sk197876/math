(** Federer (1969), 2.7.16, example (4), printed p. 138: "For 0 < m < n, the
    action of GL(n, R) on G(n, m) (see 1.6.2) admits no chi covariant
    integral, for any homomorphism chi of GL(n, R) into the multiplicative
    group R ~ {0}. In fact, if W in G(n, m) and V = R^n, the isotropy group
    GL(n, R)^W is the group studied in (3), hence Weil's condition becomes:
    chi(t) . |det(t|W)|^{-n} . |det t|^m = 1 for t in GL(n, R)^W. Since {g :
    det g = 1} is the commutator subgroup of GL(n, R), chi(g) = 1 whenever
    det g = 1. Therefore Weil's condition is violated by any t in GL(n, R)^W
    for which det t = 1 and det(t|W) <> 1." The display is transcribed from
    the page image of p. 138. Here V is a space with an inner product and a
    finite basis of n vectors, G(V, m) is the homogeneous space of GL(V) of
    LinearGrassmannAction.v, and R^n is the instance of
    EuclideanOrthogonalInvariantMeasures.v. The isotropy group of W is
    subspace_stabiliser (linear_grassmann_isotropy); by
    equal_subgroups_modular its modular function is that of example (3),
    |det(t|W)|^{-n} |det t|^m (subspace_stabiliser_modular), and
    Delta_{GL(V)} = 1 (example (2)), so that Weil's condition 2.7.11(1), p.
    128, takes the printed form (grassmann_weil_condition). By 2.7.1, p.
    122, chi is a continuous homomorphism whenever a nonzero chi covariant
    integral exists; by special_linear_commutator, chi(t) = 1 when det t =
    1. The member t of the stabiliser acting as 2^{n-m} on W and as 2^{-m}
    on a complement has det t = 1 and |det(t|W)| = 2^{m(n-m)} <> 1; Weil's
    condition would give |det(t|W)|^{-n} = 1. Federer's "det(t|W) <> 1" is
    not sufficient as printed: for t with det(t|W) = -1 the display holds;
    what is needed, and used, is |det(t|W)| <> 1 (with n > 0). The local
    erratum has no entry for this passage of p. 138. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealMetricBackground InnerProductUP InnerMetric LinearBasis TensorUP Hom HomInner
  ModuleQuotient GrassmannSubspaces CompactSupportFunctionUP DaniellIntegralUP IsotropyGroupTopology
  TopologicalGroupUP TopologicalGroupLaws HomeomorphismUP HomogeneousSpaceUP HomogeneousSpaceLaws
  CovariantIntegralUP CovariantCharacterContinuity HaarIntegralUP ModularFunctionUP ModularFunction
  WeilCondition HomSpaceTopology LinearGroupTopology LinearGroupSealed HomHaarCovariance
  LinearGroupUnimodular GrassmannHomogeneousSpace EuclideanInnerProduct FiniteCoordinates
  GrassmannAbbreviations EuclideanOrthogonalInvariantMeasures SubspaceStabiliser StabiliserModularFunction
  GroupIsomorphismModular SpecialLinearCommutators LinearGrassmannAction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section GrassmannWeil.
Variable R : realType.
Variables U V : lmodType R.
Variables (C : U -> U -> R) (B : V -> V -> R).
Hypotheses (hC : is_inner_product C) (hB : is_inner_product B).
Variables (m : nat) (c : 'I_m -> U) (n : nat) (b : 'I_n -> V).
Hypotheses (hc : is_basis c) (hb : is_basis b).
Local Notation GR := (grassmann_space hC hB hc hb).
Local Notation GL := (set_type (linear_group hB hb)).
Local Notation mul := (linear_group_mul hB hb).
Local Notation inv := (linear_group_inv hB hb).
Local Notation unit := (linear_group_unit hB hb).
Local Notation A := (linear_grassmann_action hC hB hc hb).
Local Notation KX := (@compactly_supported_continuous_functions R GR).
Local Notation Stab W := (set_type (subspace_stabiliser hB hb (grassmann_val (W : G V m)))).

(** Source for [hGL]: GL(n, R) is a locally compact Hausdorff group,
    Federer 2.7.16, p. 134, used in this section. *)
Let hGL := linear_group_operations_lch hB hb.
(** Source for [hA]: G(n, m) is a homogeneous space of GL(n, R),
    Federer 2.7.16, p. 138, used in this section. *)
Let hA : is_homogeneous_space mul A := linear_grassmann_homogeneous hC hB hc hb.
(** Source for [hX]: G(n, m) is Hausdorff, used in this section. *)
Let hX : hausdorff_space GR := (linear_grassmann_locally_compact hC hB hc hb).1.
(** Source for [hlX]: G(n, m) is locally compact, used in this
    section. *)
Let hlX : locally_compact [set: GR] := (linear_grassmann_locally_compact hC hB hc hb).2.

(** Source for [grassmann_weil_condition]: "hence Weil's condition
    becomes: chi(t) . |det(t|W)|^{-n} . |det t|^m = 1 for
    t in GL(n, R)^W", Federer 2.7.16, p. 138: for a continuous
    homomorphism chi of GL(n, R) into R ~ {0}, a nonzero chi covariant
    integral on K(G(n, m)) exists if and only if the display holds.
    Direct formalisation, by 2.7.11(1), p. 128, the isotropy group of W
    being the group of example (3) and Delta_{GL(n, R)} = 1. *)
Theorem grassmann_weil_condition (W : GR) (chi : GL -> R) :
  (forall g h, chi (mul g h) = chi g * chi h) -> (forall g, chi g != 0) ->
  continuous (chi : GL -> real_line_metric R) ->
  (exists nu : (GR -> R) -> R, is_covariant_integral A chi nu /\ exists2 v, KX v & nu v <> 0) <->
  forall t : Stab W,
    chi (set_val t) * `|stabiliser_restriction_det (grassmann_proof (W : G V m)) t| ^- n *
      `|stabiliser_det t| ^+ m = 1.
Proof.
move=> hchiM hchi0 hchic.
have [mulS [invS [eS [hR hlS]]]] := isotropy_group_exists W hGL hA hX.
have [DG hDG] := modular_function_exists R hGL.
have [DS hDS] := modular_function_exists R hlS.
rewrite (covariant_integral_exists_iff_weil hGL hA hX hlX hR hDG hDS hchiM hchi0 hchic).
have hE := @linear_grassmann_isotropy R U V C B hC hB m c n b hc hb W.
have hcl : closed (isotropy_subgroup A W) := isotropy_subgroup_closed hA hX.
have [mulT [invT [eT hT]]] := subspace_stabiliser_restriction_exists hB hb (grassmann_val (W : G V m)).
have [DT hDT] := modular_function_exists R (subspace_stabiliser_lch (grassmann_proof (W : G V m)) hT).
have hDST := equal_subgroups_modular hGL hE hcl hR hT hDS hDT.
have hDTf := subspace_stabiliser_modular (grassmann_proof (W : G V m)) hT hDT.
have hDG1 := linear_group_modular_unit hB hb hDG.
split.
- move=> hw t.
  have := hw (equal_subset_retype_inv hE t).
  rewrite hDST hDG1 hDTf -mulrA.
  have -> : equal_subset_retype hE (equal_subset_retype_inv hE t) = t by apply: val_inj.
  by [].
- move=> hw t; rewrite hDST hDG1 hDTf mulrA.
  exact: (hw (equal_subset_retype hE t)).
Qed.

(** Source for [grassmann_no_covariant_integral]: "For 0 < m < n, the
    action of GL(n, R) on G(n, m) admits no chi covariant integral, for
    any homomorphism chi of GL(n, R) into the multiplicative group
    R ~ {0}", Federer 2.7.16, p. 138, for every function chi, a nonzero
    chi covariant integral forcing chi to be a continuous homomorphism
    (2.7.1, p. 122). Direct formalisation: the member t of the
    stabiliser acting as 2^{n-m} on W and as 2^{-m} on a complement has
    det t = 1, hence chi(t) = 1 (special_linear_character_unit), and
    |det(t|W)|^{-n} = 2^{-m(n-m)n} <> 1. *)
Theorem grassmann_no_covariant_integral (chi : GL -> R) :
  (0 < m)%N -> (m < n)%N ->
  ~ exists nu : (GR -> R) -> R, is_covariant_integral A chi nu /\ exists2 v, KX v & nu v <> 0.
Proof.
move=> hm hmn hex; have [nu [hnu [v hv hnv]]] := hex.
have [hchiM _ hchi0 hchic] := covariant_character_homomorphism (lch_group_topological hGL) hA
  (lch_group_locally_compact hGL) hX hlX hnu (ex_intro _ v (conj hv hnv)).
have [W _] := nonzero_integral_point (covariant_integral_daniell hnu) (ex_intro2 _ _ v hv hnv).
have hw := (grassmann_weil_condition W hchiM hchi0 hchic).1 hex.
have h2 : (2 : R) != 0 by rewrite pnatr_eq0.
pose alpha : R := 2 ^+ (n - m).
pose beta : R := (2 ^+ m)^-1.
have ha : alpha != 0 by rewrite expf_neq0.
have hbeta : beta != 0 by rewrite invr_eq0 expf_neq0.
have [t [ht1 ht2]] := stabiliser_scaling_exists hB hb (grassmann_proof (W : G V m)) ha hbeta.
have hdet : stabiliser_det t = 1.
  rewrite ht2 /alpha /beta -!exprM mulnC exprVn -exprM.
  by rewrite mulfV // expf_neq0.
have hchi1 : chi (set_val t) = 1 := special_linear_character_unit hchiM hchi0 hdet.
have := hw t; rewrite hchi1 ht1 hdet mul1r normr1 expr1n mulr1.
have hgt : 1 < `|alpha ^+ m| ^+ n.
  rewrite normrX ger0_norm ?exprn_ge0 // /alpha -!exprM.
  rewrite exprn_egt1; last by rewrite ltrDl ltr01.
  by rewrite -lt0n !muln_gt0 subn_gt0 hmn hm (ltn_trans hm hmn).
move=> /eqP; rewrite invr_eq1 => /eqP he.
by move: hgt; rewrite he ltxx.
Qed.

End GrassmannWeil.

Section EuclideanGrassmannWeil.
Variable R : realType.
Variables n m : nat.
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation hBm := (@euclidean_inner_productP R m).
Local Notation hbm := (@coordinate_basisP R m).
Local Notation GR := (euclidean_grassmann_space R n m).
Local Notation GL := (set_type (linear_group hBn hbn)).
Local Notation KX := (@compactly_supported_continuous_functions R GR).

(** Source for [euclidean_grassmann_no_covariant_integral]: "For
    0 < m < n, the action of GL(n, R) on G(n, m) (see 1.6.2) admits no
    chi covariant integral, for any homomorphism chi of GL(n, R) into
    the multiplicative group R ~ {0}", Federer 2.7.16, p. 138, for
    R^n with the inner product of 1.7.1 and G(n, m) with the topology of
    example (6). Direct formalisation of the instance. *)
Corollary euclidean_grassmann_no_covariant_integral (chi : GL -> R) :
  (0 < m)%N -> (m < n)%N ->
  ~ exists nu : (GR -> R) -> R,
    is_covariant_integral (linear_grassmann_action hBm hBn hbm hbn) chi nu /\ exists2 v, KX v & nu v <> 0.
Proof. exact: grassmann_no_covariant_integral. Qed.

End EuclideanGrassmannWeil.
