(** Federer (1969), 3.2.47, p. 282: existence of the actual
    positively normalized finite recurrence. The public orthogonal
    residual lemmas of 1.7.1 are used; no private construction or
    arbitrary sign-chosen family is imported. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNormalization OrthonormalisationUP
  OrthonormalProjection OrthonormalExtension FinitePrefixes InfiniteSequence
  FiniteIndependence FiniteSpans FiniteSpanTransfer
  PositiveGramSchmidtUP PositiveGramSchmidtPrefixes.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_gram_schmidt_exists]: existence for the
    normalized recurrence printed in 3.2.47, p. 282, by the
    finite induction of 1.7.1, p. 28. Every residual is proved
    nonzero and every prefix span is retained. *)
Theorem positive_gram_schmidt_exists (R:rcfType) (V:lmodType R)
    B (hB:@is_inner_product R V B) n (u:'I_n->V):
  finite_independent u ->exists v,is_positive_gram_schmidt hB u v.
Proof.
elim:n u=>[|n ih] u hu.
- exists u; constructor.
  + constructor.
    * move=>i; by move:(ltn_ord i); rewrite ltn0.
    * by move=>k hk x; split.
  + move=>i; by move:(ltn_ord i); rewrite ltn0.
  + move=>i; by move:(ltn_ord i); rewrite ltn0.
- pose u0:=family_prefix (leqnSn n) u.
  have hu0:finite_independent u0:=@finite_independent_initial R V n u hu.
  have [v0 hv0]:=ih u0 hu0.
  have hOld:=positive_gram_schmidt_orthonormalisation hv0.
  have hSpan z:in_finite_span u0 z<->in_finite_span v0 z.
    exact (@orthonormalisation_span R V B n u0 v0 hOld z).
  have hOutside:~in_finite_span v0 (u ord_max).
    move=>h; apply:(@finite_independent_last_outside R V n u hu).
    exact:(hSpan _).2 h.
  pose r:=u ord_max-orthonormal_projection hB v0 (u ord_max).
  pose w:=inner_normalize hB r.
  have hNonzero:r!=0:=orthonormal_residual_nonzero hB hOutside.
  have hOrthonormal:=orthonormalisation_orthonormal hOld.
  have hNew:is_orthonormalisation B u (ordinal_snoc v0 w).
    constructor.
    + exact (@orthonormal_extensionP R V B hB n v0 hOrthonormal (u ord_max) hOutside).
    + move=>k hk z.
      case:(leqP k n)=>hkn.
      * have h1:=@finite_span_extensional R V k (family_prefix hk u)
          (family_prefix hkn u0)
          (fun i=>esym (@family_prefix_compose V k n n.+1 hkn (leqnSn n) hk u i)) z.
        have h2:=@orthonormalisation_prefix_span R V B n u0 v0 hOld k hkn z.
        have h3:=@finite_span_extensional R V k (family_prefix hkn v0)
          (family_prefix hk (ordinal_snoc v0 w))
          (fun i=>esym (@family_prefix_snoc V k n hkn hk v0 w i)) z.
        exact (iff_trans h1 (iff_trans h2 h3)).
      * have hkeq:k=n.+1 by apply/eqP; rewrite eqn_leq hk hkn.
        subst k.
        have h1:=@finite_span_extensional R V n.+1 (family_prefix hk u) u
          (@family_prefix_refl V n.+1 hk u) z.
        have h2:=@finite_span_extensional R V n.+1 u (ordinal_snoc u0 (u ord_max))
          (fun i=>esym (@family_snoc_prefix V n u i)) z.
        have h3:=@finite_span_snoc_equiv R V n n u0 v0 (u ord_max) hSpan z.
        have h4:=@finite_span_extensional R V n.+1 (ordinal_snoc v0 w)
          (family_prefix hk (ordinal_snoc v0 w))
          (fun i=>esym (@family_prefix_refl V n.+1 hk (ordinal_snoc v0 w) i)) z.
        have hExtension:=@orthonormal_extension_span R V B hB n v0
          (u ord_max) hOutside z.
        exact (iff_trans h1 (iff_trans h2 (iff_trans h3 (iff_trans hExtension h4)))).
  exists (ordinal_snoc v0 w); constructor; first exact hNew.
  + move=>i; case:(unliftP ord_max i)=>[j->|->].
    * have hj:lift ord_max j=widen_ord (leqnSn n) j by apply:val_inj; exact:lift_max.
      rewrite hj positive_gram_schmidt_residual_before.
      exact (@positive_gram_schmidt_nonzero R V B hB n u0 v0 hv0 j).
    * rewrite positive_gram_schmidt_residual_last; exact hNonzero.
  + move=>i; case:(unliftP ord_max i)=>[j->|->].
    * have hj:lift ord_max j=widen_ord (leqnSn n) j by apply:val_inj; exact:lift_max.
      rewrite hj ordinal_snoc_before positive_gram_schmidt_residual_before.
      exact (@positive_gram_schmidt_equation R V B hB n u0 v0 hv0 j).
    * by rewrite ordinal_snoc_last positive_gram_schmidt_residual_last.
Qed.
