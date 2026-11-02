(** Federer (1969), 1.7.5, p. 32: an adapted orthonormal basis for the
    simple-factor wedge estimate. The scalar factor is retained explicitly;
    it need not be one and degree zero is included. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP GramSchmidt OrthonormalFamilies
  OrthonormalisationUP FinitePrefixes FiniteSpans FiniteSpanSpace
  SimpleAdaptedBasis SimpleProducts SimpleElementary FullDegreeFactor
  AssociatedSubspace ModuleQuotient LinearBasis ExteriorGrading
  FiniteExteriorPowers ExteriorIndices InitialIndices.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [orthonormal_family_prefix]: Federer 1.7.5,
    p. 32, supporting fact: every initial segment of an
    orthonormal family is orthonormal. *)
Lemma orthonormal_family_prefix (R : fieldType) (V : lmodType R)
    (B : V -> V -> R) n (e : 'I_n -> V) (he : orthonormal_family B e)
    k (hk : (k <= n)%N) : orthonormal_family B (family_prefix hk e).
Proof.
have hi : injective (widen_ord hk).
  move=> i j h; apply: val_inj; exact (congr1 (fun a : 'I_n => (a : nat)) h).
by move=> i j; rewrite /family_prefix he (inj_eq hi).
Qed.

(** Source for [simple_orthonormal_adapted_basis]: Federer 1.7.5, p. 32,
    supporting normal form: a nonzero simple p-vector is a nonzero scalar
    times the product of the first p members of an orthonormal basis. *)
Theorem simple_orthonormal_adapted_basis (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) p (hp : (p <= n)%N)
    (x : exterior_power V p) : x != 0 -> simple x ->
  exists (d : 'I_n -> V) (c : R), is_basis d /\ orthonormal_family B d /\
    c != 0 /\ x = c *: e_lambda d (val (Lambda_initial hp)).
Proof.
move=> hx hs.
have [b [hb hxb]] := @simple_adapted_basis R V n e he p hp x hx hs.
have [d [hd hdo]] := @orthonormal_basis_exists R V B hB n b hb.
have ho := orthonormalisation_orthonormal hdo.
have hop := @orthonormal_family_prefix R V B n d ho p hp.
have hip := @orthonormal_independent R V B hB (Finite.clone 'I_p _) (family_prefix hp d) hop.
have ht i : FedererSimple.T x (family_prefix hp d i).
  rewrite hxb initial_productE; apply: product_associated_span.
  apply: (proj2 (@orthonormalisation_prefix_span R V B n b d hdo p hp _)).
  exact: (@finite_span_generator R V p (family_prefix hp d) i).
have [c [hc hxc]] := @full_degree_factor R h2 V p x (family_prefix hp d) hip ht hx.
exists d, c; split=> //; split=> //; split=> //.
by rewrite initial_productE.
Qed.
