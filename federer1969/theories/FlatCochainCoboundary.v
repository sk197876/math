(** Federer (1969), 4.1.19, p. 377: the
    actual coboundary d alpha(S)=alpha(boundary S),
    its unchanged common bound, norm nonincrease
    and d squared zero. The preceding current
    boundary laws apply on every original compact index. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentBoundary SmoothCompactSet CurrentFlatNorm
  FlatCurrentsUP FlatCurrentUnion FlatCurrentFinite FlatCurrentBoundary
  FlatCurrentUnionSpace FlatCurrentUnionBoundary CurrentFlatBoundaryFine
  FlatCochainUP FlatCochainSpace LinearSubspaceRepresentationUP
  LinearSubspaceLiftSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Coboundary.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Variable U : set (R_n R n).
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation A := (@flat_current_union_space R h2 n m U hU).
Local Notation B := (@flat_current_union_space R h2 n m.+1 U hU).
Local Notation boundary := (@flat_current_union_boundary R h2 n m U hU).
Local Notation CA := (@flat_cochain_space R h2 n m U hU).
Local Notation CB := (@flat_cochain_space R h2 n m.+1 U hU).
Local Notation EA := (@flat_cochain_evaluation R h2 n m U hU).
Local Notation EB := (@flat_cochain_evaluation R h2 n m.+1 U hU).
Local Notation NB := (@flat_cochain_norm R h2 n m.+1 U hU).
Local Notation NA := (@flat_cochain_norm R h2 n m U hU).
Local Notation hCB := (@flat_cochain_space_laws R h2 n m.+1 U hU).
Local Notation S := (@flat_cochain_subspace R h2 n m.+1 U hU).

(** Source for [flat_cochain_coboundary_common_bound]:
    every original common bound for alpha is
    valid for d alpha, Federer 4.1.19,
    p. 377. Reuse the boundary's same-K
    flat membership and sharp F_K inequality. *)
Theorem flat_cochain_coboundary_common_bound
    (alpha : Hom A R^o) (c : R) :
  @is_flat_cochain_bound R h2 n m U hU alpha c ->
  @is_flat_cochain_bound R h2 n m.+1 U hU
    (hom_comp alpha boundary) c.
Proof.
move=> [hC hAlpha]; split; first exact: hC.
move=> K T hFlat.
have hFlatBoundary : @is_flat_current_supported_in R h2 n m U hU K
    (@flat_current_union_inclusion R h2 n m U hU (boundary T)).
  rewrite flat_current_union_boundary_value.
  exact: (@flat_current_boundary_supported R h2 n m U hU K
    (@flat_current_union_inclusion R h2 n m.+1 U hU T) hFlat).
have hBound := hAlpha K (boundary T) hFlatBoundary.
rewrite flat_current_union_boundary_value in hBound.
have hFinite := @flat_current_supported_finite R h2 n m.+1 U hU K
  (@flat_current_union_inclusion R h2 n m.+1 U hU T) hFlat.
have hFine := @current_finite_flat_boundary_fine_bound R h2 n m U hU K
  (@flat_current_union_inclusion R h2 n m.+1 U hU T) hFinite.
rewrite hom_compE.
exact: (le_trans hBound (ler_wpM2l hC hFine)).
Qed.

(** Source for [flat_cochain_raw_coboundary]: the
    real-linear transpose of the original flat-current
    boundary, supporting Federer 4.1.19, p. 377.
    Its flat-cochain range is proved separately. *)
Definition flat_cochain_raw_coboundary : Hom CA (Hom B R^o) :=
  hom_comp
    (@HomMap R (Hom A R^o) (Hom B R^o)
      (fun alpha => hom_comp alpha boundary)
      (introT (asboolP _)
        (@hom_precompose_linear R B A R^o boundary))) EA.

(** Source for [flat_cochain_coboundary_range]: the
    transpose has an original finite common flat
    bound, Federer 4.1.19, p. 377.
    The already proved bound of alpha supplies
    the same real constant in every compact degree. *)
Lemma flat_cochain_coboundary_range (alpha : CA) :
  S (flat_cochain_raw_coboundary alpha).
Proof.
exists (NA alpha).
exact: (flat_cochain_coboundary_common_bound
  (@flat_cochain_norm_laws R h2 n m U hU alpha).1).
Qed.

(** Source for [flat_cochain_coboundary]: d alpha
    is an actual flat cochain, Federer 4.1.19,
    p. 377, obtained by the existing
    opaque corestriction of its proved linear transpose. *)
Definition flat_cochain_coboundary : Hom CA CB :=
  @LinearSubspaceLift.map R CA CB (Hom B R^o) S EB hCB
    flat_cochain_raw_coboundary flat_cochain_coboundary_range.

(** Source for [flat_cochain_coboundary_functional]:
    the actual coboundary has exactly its defining
    original linear functional, Federer 4.1.19,
    p. 377, on the full F_(m+1)(U). *)
Theorem flat_cochain_coboundary_functional (alpha : CA) :
  EB (flat_cochain_coboundary alpha) = hom_comp (EA alpha) boundary.
Proof.
exact: (@LinearSubspaceLift.evaluation R CA CB (Hom B R^o) S EB hCB
  flat_cochain_raw_coboundary flat_cochain_coboundary_range alpha).
Qed.

(** Source for [flat_cochain_coboundary_evaluation]:
    the literal equation d alpha(S)=alpha(boundary S),
    Federer 4.1.19, p. 377, with
    no finite-mass restriction on the original flat current. *)
Theorem flat_cochain_coboundary_evaluation (alpha : CA) (T : B) :
  EB (flat_cochain_coboundary alpha) T = EA alpha (boundary T).
Proof. by rewrite flat_cochain_coboundary_functional hom_compE. Qed.

(** Source for [flat_cochain_coboundary_norm_bound]:
    the original sharp inequality F(d alpha)<=F(alpha),
    Federer 4.1.19, p. 377, follows
    by the unchanged common bound. All natural
    degrees and empty original domains are retained. *)
Theorem flat_cochain_coboundary_norm_bound (alpha : CA) :
  NB (flat_cochain_coboundary alpha) <= NA alpha.
Proof.
apply: ((@flat_cochain_norm_laws R h2 n m.+1 U hU
  (flat_cochain_coboundary alpha)).2).
rewrite flat_cochain_coboundary_functional.
exact: (flat_cochain_coboundary_common_bound
  (@flat_cochain_norm_laws R h2 n m U hU alpha).1).
Qed.
End Coboundary.

(** Source for [flat_cochain_coboundary_squared]:
    d(d alpha)=0 in the actual cochain
    spaces, Federer 4.1.19, p. 377.
    This is the original current boundary-squared
    identity after the two literal transpose equations. *)
Theorem flat_cochain_coboundary_squared
    (R : realType) (h2 : (1+1:R)!=0) n m
    (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (alpha : @flat_cochain_space R h2 n m U hU) :
  @flat_cochain_coboundary R h2 n m.+1 U hU
    (@flat_cochain_coboundary R h2 n m U hU alpha) = 0.
Proof.
apply: (subspace_representation_injective
  (@flat_cochain_space_laws R h2 n m.+2 U hU)).
apply: hom_ext=> T; rewrite linear0 hom_zeroE.
by rewrite !flat_cochain_coboundary_evaluation
  flat_current_union_boundary_squared linear0.
Qed.
