(** Federer (1969), 1.7.1, p. 28: existence of an orthonormalisation
    preserving every initial span. This induction is an existence witness
    for OrthonormalisationUP; downstream use goes through the sealed
    interface. Source context are recorded in InnerProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP OrthonormalFamilies OrthonormalisationUP
  OrthonormalExtension FinitePrefixes FiniteIndependence FiniteSpans
  FiniteSpanTransfer InfiniteSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Construction.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.

(** Source for [gram_schmidt_witness]: Federer 1.7.1,
    p. 28, the full Gram-Schmidt assertion. The induction adds a
    normalised orthogonal residual and proves equality of every
    prefix span, including the empty and full prefixes. *)
Theorem gram_schmidt_witness n (u : 'I_n -> V) :
  finite_independent u -> exists v, is_orthonormalisation B u v.
Proof.
elim: n u => [|n ih] u hu.
- exists u; constructor.
  + move=> i; by have := ltn_ord i; rewrite ltn0.
  + by move=> k hk x; split.
- pose u0 := family_prefix (leqnSn n) u.
  have hu0 : finite_independent u0 := @finite_independent_initial R V n u hu.
  have [v0 hv0] := ih u0 hu0.
  have hspan z : in_finite_span u0 z <-> in_finite_span v0 z.
    exact (@orthonormalisation_span R V B n u0 v0 hv0 z).
  have hx : ~ in_finite_span v0 (u ord_max).
    move=> hx; apply: (@finite_independent_last_outside R V n u hu).
    exact: (proj2 (hspan _)) hx.
  have [w [hw hext]] := @orthonormal_extension_exists R V B hB n v0
    (orthonormalisation_orthonormal hv0) (u ord_max) hx.
  exists (ordinal_snoc v0 w); constructor=> // k hk z.
  case: (leqP k n) => hkn.
  + have h1 := @finite_span_extensional R V k (family_prefix hk u)
      (family_prefix hkn u0)
      (fun i => esym (@family_prefix_compose V k n n.+1 hkn (leqnSn n) hk u i)) z.
    have h2 := @orthonormalisation_prefix_span R V B n u0 v0 hv0 k hkn z.
    have h3 := @finite_span_extensional R V k (family_prefix hkn v0)
      (family_prefix hk (ordinal_snoc v0 w))
      (fun i => esym (@family_prefix_snoc V k n hkn hk v0 w i)) z.
    exact (iff_trans h1 (iff_trans h2 h3)).
  + have hkeq : k = n.+1 by apply/eqP; rewrite eqn_leq hk hkn.
    subst k.
    have h1 := @finite_span_extensional R V n.+1 (family_prefix hk u) u
      (@family_prefix_refl V n.+1 hk u) z.
    have h2 := @finite_span_extensional R V n.+1 u (ordinal_snoc u0 (u ord_max))
      (fun i => esym (@family_snoc_prefix V n u i)) z.
    have h3 := @finite_span_snoc_equiv R V n n u0 v0 (u ord_max) hspan z.
    have h4 := @finite_span_extensional R V n.+1 (ordinal_snoc v0 w)
      (family_prefix hk (ordinal_snoc v0 w))
      (fun i => esym (@family_prefix_refl V n.+1 hk (ordinal_snoc v0 w) i)) z.
    exact (iff_trans h1 (iff_trans h2 (iff_trans h3 (iff_trans (hext z) h4)))).
Qed.
End Construction.
