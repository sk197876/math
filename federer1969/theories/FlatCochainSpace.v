(** Federer (1969), 4.1.19, p. 377: the
    flat cochains form a vector space of
    linear functionals on the original F_m(U).
    Prove the common-bound subspace laws before
    applying the existing opaque subspace carrier. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ModuleQuotient RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothCompactSet CurrentFlatNorm FlatCurrentUnionSpace
  FlatCochainUP FlatCochainNormSealed LinearSubspaceRepresentationUP
  LinearSubspaceRepresentationSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section FlatCochainSpace.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Variable U : set (R_n R n).
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation W := (@flat_current_union_space R h2 n m U hU).
Local Notation A := (Hom W R^o).
Local Notation member := (@is_flat_cochain R h2 n m U hU).
Local Notation bound := (@is_flat_cochain_bound R h2 n m U hU).

(** Source for [flat_cochain_zero_bound]: the zero
    flat cochain has common bound zero, supporting
    the normed space in Federer 4.1.19,
    p. 377. Empty U and zero current
    spaces require no separate nonzero assumption. *)
Lemma flat_cochain_zero_bound : bound (0:A) 0.
Proof.
split; first exact: lexx.
move=> K T hT.
by rewrite hom_zeroE normr0 mul0r.
Qed.

(** Source for [flat_cochain_add_bound]: add the
    two original common bounds for flat cochains,
    supporting the vector space of Federer 4.1.19,
    p. 377. The same arbitrary K is
    used for both inequalities. *)
Lemma flat_cochain_add_bound (alpha beta : A) (a b : R) :
  bound alpha a -> bound beta b -> bound (alpha+beta)%R (a+b).
Proof.
move=> [hA hAlpha] [hB hBeta]; split; first exact: addr_ge0 hA hB.
move=> K T hT; rewrite hom_addE mulrDl.
exact: (le_trans (ler_normD _ _) (lerD (hAlpha K T hT) (hBeta K T hT))).
Qed.

(** Source for [flat_cochain_scale_bound]: the common
    bound scales by the absolute scalar, supporting
    the flat-cochain norm in Federer 4.1.19,
    p. 377. Scalar zero is included. *)
Lemma flat_cochain_scale_bound (alpha : A) (a c : R) :
  bound alpha a -> bound (c*:alpha)%R (`|c|*a).
Proof.
move=> [hA hAlpha]; split; first exact: mulr_ge0 (normr_ge0 c) hA.
move=> K T hT; rewrite hom_scaleE.
change (is_true (`|c*alpha T| <= (`|c|*a)*
  fine (@current_flat_norm R h2 n m U hU K
    (@flat_current_union_inclusion R h2 n m U hU T)))).
rewrite normrM -mulrA.
exact: (ler_wpM2l (normr_ge0 c) (hAlpha K T hT)).
Qed.

(** Source for [flat_cochain_subspace]: the original
    linear functionals with one finite common flat
    bound form a subspace, supporting Federer 4.1.19,
    p. 377. No compact index is chosen
    globally and no form representation is assumed. *)
Definition flat_cochain_subspace : subspace A.
Proof.
refine (@Subspace R A member _ _ _).
- exists 0; exact: flat_cochain_zero_bound.
- move=> alpha beta [a hA] [b hB].
  exists (a+b); exact: flat_cochain_add_bound hA hB.
- move=> c alpha [a hA].
  exists (`|c|*a); exact: flat_cochain_scale_bound hA.
Defined.

(** Source for [flat_cochain_space]: the actual
    space of flat cochains, Federer 4.1.19,
    p. 377, reuses the existing opaque
    representation of its independently specified subspace. *)
Definition flat_cochain_space : lmodType R :=
  @LinearSubspaceRepresentation.space R A flat_cochain_subspace.

(** Source for [flat_cochain_evaluation]: a flat
    cochain acts on the literal original flat
    current space, Federer 4.1.19, p. 377.
    The inclusion is real linear in the cochain. *)
Definition flat_cochain_evaluation : Hom flat_cochain_space A :=
  @LinearSubspaceRepresentation.inclusion R A flat_cochain_subspace.

(** Source for [flat_cochain_space_laws]: the
    opaque cochain space consists exactly of the
    original common-bound linear functionals, Federer
    4.1.19, p. 377. Its evaluation is injective. *)
Theorem flat_cochain_space_laws :
  is_linear_subspace_representation flat_cochain_subspace
    flat_cochain_evaluation.
Proof. exact: LinearSubspaceRepresentation.laws. Qed.

(** Source for [flat_cochain_norm]: the norm
    F(alpha) on the actual flat-cochain carrier,
    Federer 4.1.19, p. 377, uses
    the already opaque least common bound. *)
Definition flat_cochain_norm (alpha : flat_cochain_space) : R :=
  @FlatCochainNorm.value R h2 n m U hU (flat_cochain_evaluation alpha)
    (subspace_representation_member flat_cochain_space_laws alpha).

(** Source for [flat_cochain_norm_laws]: the
    actual cochain norm retains all original
    compact-index inequalities and their least-bound
    property, Federer 4.1.19, p. 377. *)
Theorem flat_cochain_norm_laws (alpha : flat_cochain_space) :
  @is_flat_cochain_norm R h2 n m U hU
    (flat_cochain_evaluation alpha) (flat_cochain_norm alpha).
Proof. exact: FlatCochainNorm.laws. Qed.
End FlatCochainSpace.
