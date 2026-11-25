(** Federer (1969), 4.1.12, p. 368: the
    original complete flat-current space with prescribed
    compact support. The existing opaque subspace
    representation supplies its carrier; the public
    inclusion has exactly the original flat-closure image. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom ModuleQuotient RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  SmoothCompactSet CurrentFlatNorm CurrentFiniteFlatSpace CurrentFiniteFlatOperator
  CurrentFiniteFlatCompleteness LinearSubspaceRepresentationUP LinearSubspaceRepresentationSealed
  FlatCurrentsUP FiniteFlatNormalClosure FlatCurrentClosure CompleteMetricUP
  ClosedRepresentedNormSubspace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section FlatCurrentSpaces.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable K:smooth_compact_set hNX U.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation B := (@finite_flat_current_space R h2 n m U hU K).
Local Notation incB := (@finite_flat_current_inclusion R h2 n m U hU K).
Local Notation hB := (@finite_flat_current_space_laws R h2 n m U hU K).
Local Notation NB := (@finite_flat_current_norm R h2 n m U hU K).
Local Notation hNB := (@finite_flat_current_norm_is_norm R h2 n m U hU K).
Local Notation closedB := (@finite_flat_normal_closure_subspace R h2 n m U hU K).
Local Notation F := (@current_flat_norm R h2 n m U hU K).
Local Notation originalFlat := (@flat_current_subspace R h2 n m U hU K).

(** Source for [flat_current_space]: the original
    vector space F_(m,K)(U), Federer 4.1.12,
    p. 368. Its carrier is the already sealed
    representation of the original closed subspace. *)
Definition flat_current_space:lmodType R:=
  @LinearSubspaceRepresentation.space R B closedB.

(** Source for [flat_current_finite_inclusion]: the
    original inclusion in the finite-F_K current
    space, supporting Federer 4.1.12, p. 368. *)
Definition flat_current_finite_inclusion:Hom flat_current_space B:=
  @LinearSubspaceRepresentation.inclusion R B closedB.
Local Notation incW := flat_current_finite_inclusion.
Local Notation hW := (@LinearSubspaceRepresentation.laws R B closedB).

(** Source for [flat_current_inclusion]: the original
    linear inclusion of F_(m,K)(U) into D_m(U),
    Federer 4.1.12, p. 368. *)
Definition flat_current_inclusion:Hom flat_current_space C:=hom_comp incB incW.

(** Source for [flat_current_norm]: the original
    finite F_K norm restricted to F_(m,K)(U),
    Federer 4.1.12, p. 368. Its exact agreement
    with the actual current flat value is proved below. *)
Definition flat_current_norm (z:flat_current_space):R:=NB (incW z).

(** Source for [flat_current_space_laws]: the opaque
    flat-current space has exactly the independently
    specified original approximation class as its image,
    Federer 4.1.12, p. 368. *)
Theorem flat_current_space_laws:
  is_linear_subspace_representation originalFlat flat_current_inclusion.
Proof.
constructor.
- move=>z w hEqual;apply:(subspace_representation_injective hW).
  apply:(subspace_representation_injective hB);exact:hEqual.
- move=>z.
  apply:(@finite_flat_normal_closure_iff R h2 n m U hU K (incW z)).1.
  exact:subspace_representation_member hW z.
- move=>T hFlat.
  have [b [hBImage hClosure]]:=@flat_current_closure_represents R h2 n m U hU K T hFlat.
  have [z hZ]:=subspace_representation_full hW hClosure.
  exists z;by rewrite /flat_current_inclusion hom_compE hZ hBImage.
Qed.

(** Source for [flat_current_norm_value]: the inherited
    real norm equals the original F_K of the included
    current, Federer 4.1.12, p. 368. Every flat
    value on this space is finite. *)
Lemma flat_current_norm_value z:F (flat_current_inclusion z)=(flat_current_norm z)%:E.
Proof. exact:(@finite_flat_current_norm_value R h2 n m U hU K (incW z)). Qed.

(** Source for [flat_current_norm_is_norm]: the original
    F_K on F_(m,K)(U) satisfies all norm laws,
    supporting Federer 4.1.12, p. 368. Only
    the injective original inclusion is used. *)
Theorem flat_current_norm_is_norm:is_real_norm flat_current_norm.
Proof.
exact:(@represented_subspace_norm_laws R B flat_current_space NB hNB closedB incW hW).
Qed.

(** Source for [flat_current_complete]: the original
    F_(m,K)(U) is complete relative to F_K,
    Federer 4.1.12, p. 368. Reuse completeness
    of the finite-flat space and the exact closed
    normal-subspace image, without changing the carrier. *)
Theorem flat_current_complete:
  is_complete_metric_space (real_norm_metric_space flat_current_norm_is_norm).
Proof.
have hNorm:flat_current_norm_is_norm=
  @represented_subspace_norm_laws R B flat_current_space NB hNB closedB incW hW:=Prop_irrelevance _ _.
rewrite hNorm.
apply:(@closed_represented_norm_subspace_complete R B flat_current_space NB hNB closedB incW hW).
- exact:(@finite_flat_current_complete R h2 n m U hU K).
- exact:(@finite_flat_normal_closure_closed R h2 n m U hU K).
Qed.
End FlatCurrentSpaces.
