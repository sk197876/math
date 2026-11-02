(** Federer (1969), 1.7.5, p. 32: the decomposition vi=ui+wi, with ui in the
    preceding span and wi perpendicular to it. The specification is
    independent of how the decompositions are chosen. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import InnerProductUP FinitePrefixes FiniteSpans
  FiniteFamilyOrthogonalSplit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_orthogonal_residual_family]: Federer
    1.7.5, p. 32, abstract specification of all the
    decompositions used in the displayed product identity. *)
Record is_orthogonal_residual_family (R : fieldType) (V : lmodType R)
    (B : V -> V -> R) n (v u w : 'I_n -> V) : Prop := {
  residual_family_projection : forall i,
    in_finite_span (family_prefix (ltnW (ltn_ord i)) v) (u i);
  residual_family_orthogonal : forall i y,
    in_finite_span (family_prefix (ltnW (ltn_ord i)) v) y -> B (w i) y = 0;
  residual_family_decomposition : forall i, v i = u i+w i
}.

(** Source for [orthogonal_residual_family_exists]: Federer
    1.7.5, p. 32, existence of the stated decompositions
    for any finite family, including dependent and zero vectors. *)
Theorem orthogonal_residual_family_exists (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) n (v : 'I_n -> V) :
  exists u w, is_orthogonal_residual_family B v u w.
Proof.
have h i : exists z : V*V,
    in_finite_span (family_prefix (ltnW (ltn_ord i)) v) z.1 /\
    (forall y, in_finite_span (family_prefix (ltnW (ltn_ord i)) v) y -> B z.2 y = 0) /\
    v i = z.1+z.2.
  have [u [w [hu [hw hv]]]] := @finite_family_orthogonal_split R V B hB i
    (family_prefix (ltnW (ltn_ord i)) v) (v i).
  by exists (u,w).
pose z i := sval (constructive_indefinite_description (h i)).
have hz i := svalP (constructive_indefinite_description (h i)).
exists (fun i => (z i).1), (fun i => (z i).2); constructor.
- move=> i; exact (proj1 (hz i)).
- move=> i; exact (proj1 (proj2 (hz i))).
- move=> i; exact (proj2 (proj2 (hz i))).
Qed.
