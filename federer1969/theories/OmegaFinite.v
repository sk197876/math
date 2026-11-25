(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From Federer Require Import AlternatingCoordinates.
From Federer Require Import OneFormIdentification OmegaConstruction BasisMap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.4: Omega sends exterior products of covectors to their
    alternating products, exactly as in the proof of injectivity. *)
Section Products.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable n : nat.
Variable omega : 'I_n -> Hom V K^o.
(** Source for [Omega_e_lambda]: Federer (1969), 1.4.4, p. 19, opening
    construction of Omega. In words: The identification of linear
    functionals with one-covectors extends uniquely to a unit-preserving
    algebra homomorphism from the exterior algebra of the dual to the
    alternating algebra. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Lemma Omega_e_lambda m (lambda : Lambda n m) :
  Omega_m h2 (e_lambda omega (val lambda)) =
    omega_lambda h2 (fun i => one_form (omega i)) lambda.
Proof.
apply: (can_inj (@form_includeK K V K^o m)).
rewrite Omega_m_include e_lambdaE /Omega Omega_W_word omega_lambda_include.
change (foldr (alternating_wedge h2 (scalar_bilinear K)) (coefficient_form V (1 : K^o))
  [seq one_generator a | a <- [seq omega i | i <- val lambda]] =
  foldr (alternating_wedge h2 (scalar_bilinear K)) (coefficient_form V (1 : K^o))
  [seq one_generator (omega i) | i <- val lambda]).
by rewrite -map_comp.
Qed.
End Products.

(** Federer 1.4.4: in finite dimension, both degree-m spaces have
    dimension binomial(n,m), and the indicated products are bases. *)
Section Finite.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Local Notation omega := (dual_basis he).
Local Notation omega_forms := (fun i => one_form (omega i)).
(** Source for [finite_dual_biorthogonal]: Federer (1969), 1.4.4, p. 20,
    opening finite-dimensional epimorphism assertion. In words: When V is
    finite dimensional, Omega is surjective: in each degree the source and
    target have the same binomial dimension. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma finite_dual_biorthogonal i j : omega_forms i [tuple e j] = if i == j then 1 else 0.
Proof. by rewrite one_formE dual_basisE eq_sym. Qed.
(** Source for [Omega_image_basis]: Federer (1969), 1.4.4, p. 20, opening
    finite-dimensional epimorphism assertion. In words: When V is finite
    dimensional, Omega is surjective: in each degree the source and target
    have the same binomial dimension. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma Omega_image_basis m : is_basis
  (fun lambda : Lambda n m => Omega_m h2 (e_lambda omega (val lambda))).
Proof.
apply: (basis_congr (fun lambda => esym (Omega_e_lambda h2 omega lambda))).
exact (@omega_lambda_basis K h2 V n m e omega_forms he finite_dual_biorthogonal).
Qed.
(** Source for [Omega_m_finite_injective]: Federer (1969), 1.4.4, p. 19,
    monomorphism assertion and basis argument. In words: Omega is injective
    because it takes exterior products of independent covectors to their
    independent alternating products. Supporting lemma for this passage; not
    separately stated in the book. *)
Theorem Omega_m_finite_injective m : injective (@Omega_m K h2 V m).
Proof.
exact (@basis_map_injective K (Choice.clone (Lambda n m) _)
  (exterior_power (Hom V K^o) m) (A_m V K^o m)
  (fun lambda => e_lambda omega (val lambda)) (finite_e_lambda_basis (dual_basisP he) h2 m)
  (GRing.Linear.clone _ _ _ _ (@Omega_m K h2 V m) _) (Omega_image_basis m)).
Qed.
(** Source for [Omega_m_finite_surjective]: Federer (1969), 1.4.4, p. 20,
    opening finite-dimensional epimorphism assertion. In words: When V is
    finite dimensional, Omega is surjective: in each degree the source and
    target have the same binomial dimension. Formalises the indicated part
    of the passage under the hypotheses in the statement below. *)
Theorem Omega_m_finite_surjective m : forall phi : A_m V K^o m,
  exists xi, Omega_m h2 xi = phi.
Proof.
exact (@basis_map_surjective K (Choice.clone (Lambda n m) _)
  (exterior_power (Hom V K^o) m) (A_m V K^o m)
  (fun lambda => e_lambda omega (val lambda)) 
  (GRing.Linear.clone _ _ _ _ (@Omega_m K h2 V m) _) (Omega_image_basis m)).
Qed.
(** Source for [Omega_finite_dimensions]: Federer (1969), 1.4.4, p. 20,
    opening finite-dimensional epimorphism assertion. In words: When V is
    finite dimensional, Omega is surjective: in each degree the source and
    target have the same binomial dimension. Formalises the indicated part
    of the passage under the hypotheses in the statement below. *)
Theorem Omega_finite_dimensions m :
  dim (finite_exterior_power h2 (dual_basisP he) m) = 'C(n,m) /\
  dim (finite_form_power h2 he m) = 'C(n,m).
Proof. by rewrite exterior_power_dimension form_power_dimension. Qed.
(** Source for [Omega_finite_surjective]: Federer (1969), 1.4.4, p. 20,
    opening finite-dimensional epimorphism assertion. In words: When V is
    finite dimensional, Omega is surjective: in each degree the source and
    target have the same binomial dimension. Formalises the indicated part
    of the passage under the hypotheses in the statement below. *)
Theorem Omega_finite_surjective : forall phi : A_star V K^o, exists xi, Omega h2 V xi = phi.
Proof.
apply: alternating_sum_induction.
- exists 0; exact: linear0.
- move=> phi psi [x hx] [y hy]; exists (x+y); by rewrite linearD hx hy.
- move=> m phi; have [x hx] := Omega_m_finite_surjective phi.
  exists (component_val x); by rewrite -Omega_m_include hx.
Qed.
End Finite.
