(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From Federer Require Import AlternatingCoordinates.
From Federer Require Import OneFormIdentification OmegaConstruction OmegaFinite OmegaComponents
  OmegaNaturality ExteriorFiniteSupport FiniteEvaluation FiniteEvaluationMaps.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.4: Omega is a monomorphism for every V. An element
    involves finitely many covectors; recover these from finitely many
    evaluations and apply the proved finite-dimensional assertion.
    This implements the finite-support content of the book's basis
    argument without assuming that V or its dual has a countable basis. *)
Section Injectivity.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
(** Source for [Omega_kernel]: Federer (1969), 1.4.4, p. 19, monomorphism
    assertion and basis argument. In words: Omega is injective because it
    takes exterior products of independent covectors to their independent
    alternating products. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma Omega_kernel (x : exterior_space (Hom V K^o)) : Omega h2 V x = 0 -> x = 0.
Proof.
move=> hx; have [s hs] := exterior_finite_support x.
have [n [e [omega he]]] := finite_evaluation_reconstruction s.
pose C := coordinate_space K n.
pose f := point_synthesis e.
pose d : {linear Hom V K^o -> Hom C K^o} :=
  GRing.Linear.clone _ _ _ _ (@Hom_dual K C V (scalar_algebra K) f) _.
pose k : {linear Hom C K^o -> Hom V K^o} :=
  GRing.Linear.clone _ _ _ _ (covector_extension omega) _.
have hfix : exterior_algebra_map (linear_comp k d) x = x.
  apply: hs => a ha.
  change (covector_extension omega (@Hom_dual K C V (scalar_algebra K) f a) = a).
  rewrite finite_evaluation_factorisation; exact: he ha.
have hz : exterior_algebra_map d x = 0.
  apply (@Omega_finite_injective K h2 C n (@coordinate_basis K n) (coordinate_basisP K n)).
  rewrite linear0.
  have hn := @Omega_W_natural K h2 C V (scalar_algebra K) f (@mulrC K) x.
  change (A_star_dual f (Omega h2 V x) = Omega h2 C (exterior_algebra_map d x)) in hn.
  by rewrite -hn hx linear0.
have hk := congr1 (fun y => exterior_algebra_map k y) hz.
by rewrite exterior_algebra_map_comp hfix linear0 in hk.
Qed.
(** Source for [Omega_injective]: Federer (1969), 1.4.4, p. 19, monomorphism
    assertion and basis argument. In words: Omega is injective because it
    takes exterior products of independent covectors to their independent
    alternating products. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Theorem Omega_injective : injective (Omega h2 V).
Proof.
move=> x y h; apply/eqP; rewrite -subr_eq0; apply/eqP; apply: Omega_kernel.
by rewrite linearB h subrr.
Qed.
(** Source for [Omega_m_injective]: Federer (1969), 1.4.4, p. 19,
    monomorphism assertion and basis argument. In words: Omega is injective
    because it takes exterior products of independent covectors to their
    independent alternating products. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem Omega_m_injective m : injective (@Omega_m K h2 V m).
Proof.
move=> x y h; apply: val_inj; apply: Omega_injective.
have hi := congr1 (@form_include K V K^o m) h.
by rewrite !Omega_m_include in hi.
Qed.
End Injectivity.
