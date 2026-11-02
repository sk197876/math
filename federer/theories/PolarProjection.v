(** Federer (1969), 1.7.3, p. 30, final assertion: the orthogonal-projection
    factorisation follows by applying the injection factorisation to the
    adjoint. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP OrthonormalFamilies GramSchmidt
  OrthonormalisationUP FiniteIndependence LinearBasis AdjointUP Adjoint
  AdjointLaws PolarFactorisationUP PolarInjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [polar_projection_factorisation_exists]: Federer
    1.7.3, p. 30, if dim V is at least dim U, then f=k composed
    with p for symmetric k on U and an orthogonal projection p
    from V to U. Both dimensions here are specified by arbitrary bases. *)
Theorem polar_projection_factorisation_exists (R : realType) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (b : 'I_n -> V) (hb : is_basis b)
    m (c : 'I_m -> U) (hc : is_basis c) (hmn : (m <= n)%N)
    (f : {linear V -> U}) :
  exists (k : {linear U -> U}) (p : {linear V -> U}),
    is_projection_factorisation B C f k p.
Proof.
have [e [he hgs]] := @orthonormal_basis_exists R V B hB n b hb.
have ho := orthonormalisation_orthonormal hgs.
pose u := fun i : 'I_m => e (widen_ord hmn i).
have hw : injective (widen_ord hmn).
  move=> i j hij; apply: val_inj; exact (congr1 val hij).
have huo : orthonormal_family B u.
  by move=> i j; rewrite /u ho (inj_eq hw).
have hu := @orthonormal_independent R V B hB (Finite.clone 'I_m _) u huo.
pose a := inner_adjoint hB hC hb f.
have ha0 := @inner_adjointP R V U B C hB hC n b hb f.
have ha := @adjoint_reverse R V U B C hB hC f a ha0.
have [k [h hkh]] := @polar_injection_factorisation_exists R U V C B hC hB m c hc u hu a.
pose p := inner_adjoint hC hB hc h.
have hp := @inner_adjointP R U V C B hC hB m c hc h.
have hk := injection_factor_symmetric hkh.
have hh := injection_factor_equation hkh.
exists k, p; constructor.
- exact hk.
- exists h; split; [exact: injection_factor_orthogonal hkh | exact hp].
- move=> x; apply: (@inner_vectors_ext R U C hC) => y.
  by rewrite -hk hp hh -ha.
Qed.
