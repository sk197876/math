(** Federer (1969), 1.7.1, p. 28: the required properties of an
    orthonormalisation of an independent finite sequence. This specification
    includes every prefix, not just the full span. Source context are
    recorded in InnerProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import OrthonormalFamilies FinitePrefixes FiniteSpans FiniteSpanTransfer.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_orthonormalisation]: Federer 1.7.1,
    p. 28, the full assertion about v_1,...,v_p: orthonormality
    and equality of the spans of u_1,...,u_k and v_1,...,v_k
    for each k. The empty prefix is included. *)
Record is_orthonormalisation (R : fieldType) (V : lmodType R)
  (B : V -> V -> R) n (u v : 'I_n -> V) : Prop := {
  orthonormalisation_orthonormal : orthonormal_family B v;
  orthonormalisation_prefix_span : forall k (hk : (k <= n)%N) x,
    in_finite_span (family_prefix hk u) x <-> in_finite_span (family_prefix hk v) x
}.

(** Source for [orthonormalisation_span]: Federer 1.7.1,
    p. 28, the full spans coincide as the final case of prefix preservation. *)
Lemma orthonormalisation_span (R : fieldType) (V : lmodType R)
  (B : V -> V -> R) n (u v : 'I_n -> V) :
  is_orthonormalisation B u v -> forall x, in_finite_span u x <-> in_finite_span v x.
Proof.
move=> h x.
have hu := @finite_span_extensional R V n (family_prefix (leqnn n) u) u
  (@family_prefix_refl V n (leqnn n) u) x.
have hv := @finite_span_extensional R V n (family_prefix (leqnn n) v) v
  (@family_prefix_refl V n (leqnn n) v) x.
exact (iff_trans (iff_sym hu)
  (iff_trans (@orthonormalisation_prefix_span R V B n u v h n (leqnn n) x) hv)).
Qed.
