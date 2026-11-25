(** Federer (1969), 1.7.5, pp. 32-33: exterior products of an orthonormal
    family are orthonormal; gamma sends them to the corresponding products
    of dual covectors. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerPolarity InnerExterior
  InnerExteriorProducts OrthonormalFamilies OrthonormalBilinearCoordinates
  LinearBasis FiniteExteriorPowers ExteriorIndices
  AlternatingCoordinates OneFormProducts CovectorProducts ScalarCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Basis.
Variable R : realFieldType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.

(** Source for [inner_exterior_basis_covectors]: Federer
    1.7.5, p. 33, gamma_m(e_lambda)=omega_lambda when
    omega_i=beta(e_i); on an orthonormal basis these are its
    dual covectors. The product identity itself holds for any family.
    Normalisation clarification: the printed sentence says dual
    orthogonal bases, but identifying beta(e_i) with the algebraic
    dual basis requires unit lengths. Indeed beta(e_i)(e_i)=|e_i|^2,
    whereas the dual basis evaluates to one. This is a local
    clarification; the May 1987 erratum has no p. 33 correction. *)
Lemma inner_exterior_basis_covectors m (lambda : Lambda n m) :
  inner_exterior_form h2 hB (e_lambda e (val lambda)) =
    omega_lambda h2 (fun i => inner_polarity hB (e i)) lambda.
Proof.
apply: (can_inj (@form_includeK R V R^o m)).
rewrite inner_exterior_form_include e_lambdaE inner_exterior_word omega_lambda_include.
by rewrite -map_comp.
Qed.

Hypothesis he : orthonormal_family B e.

(** Source for [exterior_orthonormal_family]: Federer 1.7.5,
    p. 32, the increasing exterior products of an orthonormal
    family form an orthonormal family in each degree. *)
Theorem exterior_orthonormal_family m :
  orthonormal_family (@exterior_inner_form R h2 V B hB m)
    (fun lambda : Lambda n m => e_lambda e (val lambda)).
Proof.
have hd i j : inner_polarity hB (e i) [tuple e j] = if i==j then 1 else 0.
  by rewrite inner_polarityE he eq_sym.
move=> lambda mu; rewrite /exterior_inner_form inner_exterior_basis_covectors.
by rewrite (@pairing_e_omega R h2 V n m (fun i => inner_polarity hB (e i)) e hd) eq_sym.
Qed.

(** Source for [finite_exterior_inner_product]: Federer
    1.7.5, p. 32, positivity and symmetry in finite dimension
    follow from the orthonormal exterior basis and coordinate squares. *)
Theorem finite_exterior_inner_product (hb : is_basis e) m :
  is_inner_product (@exterior_inner_form R h2 V B hB m).
Proof.
apply: (@orthonormal_basis_inner_product R (exterior_power V m)
  (@exterior_inner_form R h2 V B hB m) (exterior_inner_form_bilinear h2 hB m)
  (Finite.clone (Lambda n m) _) (fun lambda => e_lambda e (val lambda))).
- exact: exterior_orthonormal_family.
- exact (@finite_e_lambda_basis R n V e hb h2 m).
Qed.
End Basis.
