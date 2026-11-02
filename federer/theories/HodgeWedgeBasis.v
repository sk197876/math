(** Federer (1969), 1.7.8, p. 34: xi wedge star(eta) equals their inner
    product times the chosen unit volume. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerPolarity InnerExterior
  OrthonormalFamilies LinearBasis ExteriorGrading GradedComponents
  AlternatingCoordinates AlternatingPairing FiniteExteriorPowers CovectorProducts
  CovectorBasisSeparation ExteriorDeterminant TopComplements DualityMaps
  DualityBasis DualityInverse ExteriorHomogeneousProducts HomogeneousHom Hom
  HodgeMaps TensorUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Wedge.
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
Local Notation Omega := (omega_lambda h2 omega (Lambda_top n)).

(** Source for [hodge_vector_wedge_basis_volume]: Federer 1.7.8,
    p. 34, second conclusion, first for the top product of
    an orthonormal basis. The reindexing only identifies p+(n-p)=n. *)
Theorem hodge_vector_wedge_basis_volume p (hp : (p <= n)%N)
    (x y : exterior_power V p) :
  exterior_reindex (subnKC hp) (exterior_product x (hodge_vector h2 hB E hp y)) =
    exterior_inner_form h2 hB x y *: E.
Proof.
have hd i j : omega i [tuple e j] = if i == j then 1 else 0.
  by rewrite inner_polarityE ho eq_sym.
have hk := @D_upperK R h2 V n e omega he hd p hp (inner_exterior_form h2 hB y).
have hh := congr1 (fun a : A_m V R^o p => form_homogeneous a (component_val x)) hk.
rewrite /D_upper_inverse form_reindexE D_pE in hh.
apply: (@pairing_covector_basis_ext R h2 V n n e omega he hd) => lambda.
rewrite (Lambda_top_unique lambda) (bilZl (@pairing_bilinear R V R^o n))
  (@top_dual_pair R h2 V n e omega hd).
change (form_homogeneous Omega
  (component_val (exterior_reindex (subnKC hp)
    (exterior_product x (hodge_vector h2 hB E hp y)))) =
  exterior_inner_form h2 hB x y * 1).
rewrite exterior_reindexE exterior_productE mulr1.
exact hh.
Qed.
End Wedge.
