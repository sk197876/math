(** Federer (1969), 4.1.12, p. 367: the
    original finite-flat current subspace. Its carrier
    is the existing opaque representation of the
    independently defined finite-F_K class. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import Hom ModuleQuotient RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces SmoothCompactSet CurrentFlatNorm
  LinearSubspaceRepresentationUP LinearSubspaceRepresentationSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentFiniteFlatSpace.
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
Local Notation F := (@current_flat_norm R h2 n m U hU K).

(** Source for [finite_flat_current_subspace]: the
    original class D_m(U) intersect {T:F_K(T)<infinity}
    is a vector subspace, Federer 4.1.12, p. 367.
    Membership is precisely the original finite bound. *)
Definition finite_flat_current_subspace:subspace C.
Proof.
refine (@Subspace R C (fun T=>(F T < +oo)%E) _ _ _).
- rewrite current_flat_norm_zero;change (((0:R)%:E < +oo)%E);exact:ltry.
- move=>T S hT hS.
  have h:=@current_flat_finite_linear_combination R h2 n m U hU K 1 T S hT hS.
  by rewrite scale1r in h.
- move=>c T hT.
  have hZero:(F (0:C) < +oo)%E by rewrite current_flat_norm_zero;change (((0:R)%:E < +oo)%E);exact:ltry.
  have h:=@current_flat_finite_linear_combination R h2 n m U hU K c T 0 hT hZero.
  by rewrite addr0 in h.
Defined.

(** Source for [finite_flat_current_space]: the actual
    finite-flat current space with its opaque exact
    subspace carrier, Federer 4.1.12, p. 367. *)
Definition finite_flat_current_space:lmodType R:=
  @LinearSubspaceRepresentation.space R C finite_flat_current_subspace.

(** Source for [finite_flat_current_inclusion]: the
    original linear inclusion of finite-flat currents
    into D_m(U), Federer 4.1.12, p. 367. *)
Definition finite_flat_current_inclusion:Hom finite_flat_current_space C:=
  @LinearSubspaceRepresentation.inclusion R C finite_flat_current_subspace.

(** Source for [finite_flat_current_space_laws]: the
    carrier represents exactly all original finite-
    F_K currents, Federer 4.1.12, p. 367. *)
Theorem finite_flat_current_space_laws:
  is_linear_subspace_representation finite_flat_current_subspace finite_flat_current_inclusion.
Proof. exact:LinearSubspaceRepresentation.laws. Qed.

(** Source for [finite_flat_current_norm]: the original
    finite value F_K on its actual subspace,
    supporting the completeness assertion of Federer
    4.1.12, p. 367. Its norm laws are proved later. *)
Definition finite_flat_current_norm (T:finite_flat_current_space):R:=
  fine (F (finite_flat_current_inclusion T)).
End CurrentFiniteFlatSpace.
