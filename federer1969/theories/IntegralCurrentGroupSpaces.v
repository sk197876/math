(** Federer (1969), 4.1.24, pp. 380–381:
    the original rectifiable, integral and integral-flat
    groups, at one compact index and on the full
    compact unions. Their carriers reuse the independently
    specified opaque additive-subgroup representation. Only
    additive inclusions and exact-image laws are exposed;
    no real vector-space structure is imposed on these
    integer groups. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces TopologicalGroupUP
  AdditiveSubgroupRepresentationUP AdditiveSubgroupRepresentationSealed
  RectifiableCurrentApproximationUP RectifiableCurrentAlgebra
  IntegralCurrentClassesUP IntegralCurrentAlgebra IntegralCurrentUnionGroups.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section IntegralCurrentGroupSpaces.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation V:=C.
Local Notation Rect:=(@is_rectifiable_current_supported_in R h2 n m U hU K).
Local Notation Int:=(@is_integral_current_supported_in R h2 n U hU m K).
Local Notation IF:=(@is_integral_flat_current_supported_in R h2 n U hU m K).
Local Notation hRect:=(@rectifiable_current_subgroup R h2 n m U hU K).
Local Notation hInt:=(@integral_current_subgroup_supported R h2 n U hU K m).
Local Notation hIF:=(@integral_flat_current_subgroup_supported R h2 n U hU K m).

(** Source for [rectifiable_current_group]: the actual original
    R_(m,K) additive carrier, 4.1.24, p. 380. *)
Definition rectifiable_current_group:zmodType:=@AdditiveSubgroupRepresentation.space V Rect hRect.
(** Source for [rectifiable_current_inclusion]: the original
    additive current inclusion, 4.1.24, p. 380. *)
Definition rectifiable_current_inclusion:{additive rectifiable_current_group->C}:=
  @AdditiveSubgroupRepresentation.inclusion V Rect hRect.
(** Source for [rectifiable_current_group_laws]: exactly the
    independently defined original approximation class is
    represented, 4.1.24, p. 380. *)
Theorem rectifiable_current_group_laws:
  is_additive_subgroup_representation Rect rectifiable_current_inclusion.
Proof. exact:AdditiveSubgroupRepresentation.laws. Qed.

(** Source for [integral_current_group]: the original I_(m,K)
    additive carrier, with the original separate degree-zero
    definition, 4.1.24, p. 381. *)
Definition integral_current_group:zmodType:=@AdditiveSubgroupRepresentation.space V Int hInt.
(** Source for [integral_current_inclusion]: the original additive
    integral-current inclusion, 4.1.24, p. 381. *)
Definition integral_current_inclusion:{additive integral_current_group->C}:=
  @AdditiveSubgroupRepresentation.inclusion V Int hInt.
(** Source for [integral_current_group_laws]: the opaque integral
    carrier has exactly the original two rectifiable
    conditions in positive degree, 4.1.24, p. 381. *)
Theorem integral_current_group_laws:
  is_additive_subgroup_representation Int integral_current_inclusion.
Proof. exact:AdditiveSubgroupRepresentation.laws. Qed.

(** Source for [integral_flat_current_group]: the original
    integral-flat additive carrier, 4.1.24, p. 381. *)
Definition integral_flat_current_group:zmodType:=@AdditiveSubgroupRepresentation.space V IF hIF.
(** Source for [integral_flat_current_inclusion]: the original
    additive integral-flat inclusion, 4.1.24, p. 381. *)
Definition integral_flat_current_inclusion:{additive integral_flat_current_group->C}:=
  @AdditiveSubgroupRepresentation.inclusion V IF hIF.
(** Source for [integral_flat_current_group_laws]: its image is
    exactly every original same-K rectifiable decomposition,
    4.1.24, p. 381. *)
Theorem integral_flat_current_group_laws:
  is_additive_subgroup_representation IF integral_flat_current_inclusion.
Proof. exact:AdditiveSubgroupRepresentation.laws. Qed.

Local Notation GlobalRect:=(@is_rectifiable_current R h2 n U hU m).
Local Notation GlobalInt:=(@is_integral_current R h2 n U hU m).
Local Notation GlobalIF:=(@is_integral_flat_current R h2 n U hU m).
Local Notation hGlobalRect:=(@rectifiable_current_union_subgroup R h2 n m U hU).
Local Notation hGlobalInt:=(@integral_current_union_subgroup R h2 n m U hU).
Local Notation hGlobalIF:=(@integral_flat_current_union_subgroup R h2 n m U hU).

(** Source for [global_rectifiable_current_group]: the literal
    compact union R_m(U) as an opaque additive group,
    4.1.24, pp. 380–381. *)
Definition global_rectifiable_current_group:zmodType:=
  @AdditiveSubgroupRepresentation.space V GlobalRect hGlobalRect.
(** Source for [global_rectifiable_current_inclusion]: the original
    compact-union rectifiable inclusion, 4.1.24, p. 381. *)
Definition global_rectifiable_current_inclusion:{additive global_rectifiable_current_group->C}:=
  @AdditiveSubgroupRepresentation.inclusion V GlobalRect hGlobalRect.
(** Source for [global_rectifiable_current_group_laws]: every original
    compact witness and only those witnesses are represented,
    4.1.24, p. 381. *)
Theorem global_rectifiable_current_group_laws:
  is_additive_subgroup_representation GlobalRect global_rectifiable_current_inclusion.
Proof. exact:AdditiveSubgroupRepresentation.laws. Qed.

(** Source for [global_integral_current_group]: the original I_m(U)
    compact union is an opaque additive group,
    4.1.24, p. 381. *)
Definition global_integral_current_group:zmodType:=
  @AdditiveSubgroupRepresentation.space V GlobalInt hGlobalInt.
(** Source for [global_integral_current_inclusion]: its original
    additive inclusion into currents, 4.1.24, p. 381. *)
Definition global_integral_current_inclusion:{additive global_integral_current_group->C}:=
  @AdditiveSubgroupRepresentation.inclusion V GlobalInt hGlobalInt.
(** Source for [global_integral_current_group_laws]: the exact original
    union of integral groups, 4.1.24, p. 381. *)
Theorem global_integral_current_group_laws:
  is_additive_subgroup_representation GlobalInt global_integral_current_inclusion.
Proof. exact:AdditiveSubgroupRepresentation.laws. Qed.

(** Source for [global_integral_flat_current_group]: the original
    integral-flat compact union carrier, 4.1.24, p. 381. *)
Definition global_integral_flat_current_group:zmodType:=
  @AdditiveSubgroupRepresentation.space V GlobalIF hGlobalIF.
(** Source for [global_integral_flat_current_inclusion]: its original
    additive current inclusion, 4.1.24, p. 381. *)
Definition global_integral_flat_current_inclusion:{additive global_integral_flat_current_group->C}:=
  @AdditiveSubgroupRepresentation.inclusion V GlobalIF hGlobalIF.
(** Source for [global_integral_flat_current_group_laws]: exact original
    compact-union integral-flat membership, 4.1.24, p. 381. *)
Theorem global_integral_flat_current_group_laws:
  is_additive_subgroup_representation GlobalIF global_integral_flat_current_inclusion.
Proof. exact:AdditiveSubgroupRepresentation.laws. Qed.
End IntegralCurrentGroupSpaces.
