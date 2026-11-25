(** Federer (1969), 1.7.8, p. 34: simultaneous Hodge stars preserve the
    vector/covector pairing. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerPolarity InnerExterior
  OrthonormalFamilies LinearBasis ExteriorGrading AlternatingCoordinates
  AlternatingPairing FiniteExteriorPowers CovectorProducts CovectorWords GrassmannCoordinates
  TopComplements InteriorSigns HodgeMaps HodgeBasis HodgeComplement
  TensorUP Bilinear BilinearPrecompose BilinearBasisExt.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Pairing.
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

(** Source for [hodge_pairing_basis_volume]: Federer 1.7.8,
    p. 34, fifth conclusion: simultaneous stars preserve the
    pairing, first for the top product of an orthonormal basis. *)
Theorem hodge_pairing_basis_volume p (hp : (p <= n)%N)
    (x : exterior_power V p) (phi : A_m V R^o p) :
  pairing (hodge_vector h2 hB E hp x) (hodge_covector h2 hB E hp phi) = pairing x phi.
Proof.
have hd i j : omega i [tuple e j] = if i == j then 1 else 0.
  by rewrite inner_polarityE ho eq_sym.
pose S := GRing.Linear.clone _ _ _ _ (@hodge_vector R h2 V B hB n E p hp) _.
pose C := GRing.Linear.clone _ _ _ _ (@hodge_covector R h2 V B hB n E p hp) _.
change (pairing (S x) (C phi) = pairing x phi).
refine (@bilinear_basis_ext R (Choice.clone (Lambda n p) _) (Choice.clone (Lambda n p) _)
  (exterior_power V p) (A_m V R^o p) R^o
  (fun lambda => e_lambda e (val lambda)) (@omega_lambda R h2 V n omega p)
  (finite_e_lambda_basis he h2 p) (@omega_lambda_basis R h2 V n p e omega he hd)
  (fun x phi => pairing (S x) (C phi)) (@pairing R V R^o p)
  (bilinear_linear_precompose (@pairing_bilinear R V R^o (n-p)) S C)
  (@pairing_bilinear R V R^o p) _ x phi).
move=> lambda mu.
change (pairing (hodge_vector h2 hB E hp (e_lambda e (val lambda)))
  (hodge_covector h2 hB E hp (omega_lambda h2 omega mu)) =
  pairing (e_lambda e (val lambda)) (omega_lambda h2 omega mu)).
rewrite (hodge_vector_basis h2 hB he ho) (hodge_covector_basis h2 hB he ho)
  (bilZl (@pairing_bilinear R V R^o (n-p)))
  (bilZr (@pairing_bilinear R V R^o (n-p)))
  !(pairing_e_omega h2 hd) (inj_eq (@top_complement_injective n p)).
have [->|hne] := eqVneq lambda mu.
- change ((-1 : R)^+(FedererInteriorSigns.N mu (top_complement mu)) *
    ((-1 : R)^+(FedererInteriorSigns.N mu (top_complement mu)) * 1) = 1).
  by rewrite mulr1 -exprMn mulrNN mul1r expr1n.
- by rewrite ?(negbTE hne) ?scaler0.
Qed.
End Pairing.
