(** Federer (1969), 1.7.8, p. 34: complementary-basis formulas for the Hodge
    maps. The basis is explicitly orthonormal, so beta(e_i) is its dual
    basis. No arbitrary nonorthonormal dual basis is substituted. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerPolarity InnerExterior
  InnerExteriorBasis OrthonormalFamilies LinearBasis ExteriorGrading
  AlternatingCoordinates FiniteExteriorPowers CovectorProducts
  DualityMaps DualityBasis TopComplements InteriorSigns InteriorComplements
  HodgeMaps.
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
Hypothesis he : is_basis e.
Hypothesis ho : orthonormal_family B e.
Local Notation E := (e_lambda e (val (Lambda_top n))).
Local Notation omega := (fun i => inner_polarity hB (e i)).

(** Source for [hodge_vector_basis]: Federer 1.7.8,
    p. 34, first basis formula: star(e_lambda) is (-1)^N
    times the complementary basis product. N is the inversion
    count already defined in 1.5.2. *)
Theorem hodge_vector_basis p (hp : (p <= n)%N) (lambda : Lambda n p) :
  hodge_vector h2 hB E hp (e_lambda e (val lambda)) =
    (-1 : R)^+(FedererInteriorSigns.N lambda (top_complement lambda)) *:
      e_lambda e (val (top_complement lambda)).
Proof.
have hd i j : omega i [tuple e j] = if i == j then 1 else 0.
  by rewrite inner_polarityE ho eq_sym.
rewrite /hodge_vector inner_exterior_basis_covectors.
exact: (@D_upper_basis R h2 V n e omega he hd p hp lambda).
Qed.

(** Source for [hodge_covector_basis]: Federer 1.7.8,
    p. 34, second basis formula: star(omega_lambda) is
    (-1)^N times the complementary dual basis product. *)
Theorem hodge_covector_basis p (hp : (p <= n)%N) (lambda : Lambda n p) :
  hodge_covector h2 hB E hp (omega_lambda h2 omega lambda) =
    (-1 : R)^+(FedererInteriorSigns.N lambda (top_complement lambda)) *:
      omega_lambda h2 omega (top_complement lambda).
Proof.
have hd i j : omega i [tuple e j] = if i == j then 1 else 0.
  by rewrite inner_polarityE ho eq_sym.
rewrite /hodge_covector (@D_upper_basis R h2 V n e omega he hd p hp lambda) linearZ.
exact (congr1 (fun z : A_m V R^o (n-p) =>
  (-1 : R)^+(FedererInteriorSigns.N lambda (top_complement lambda)) *: z)
  (@inner_exterior_basis_covectors R h2 V B hB n e (n-p) (top_complement lambda))).
Qed.
End Basis.
