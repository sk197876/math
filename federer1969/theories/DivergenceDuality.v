(** Federer (1969), 4.1.6, p. 354: the
    original duality identity for actual differentiable
    multivector fields. Finite-dimensional boundedness
    of D_p connects the proved algebraic identity
    to the genuine first differential. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialFiniteCalculus
  NormFiniteLinearBound FiniteOrdinalBasis FiniteExteriorPowers ExteriorIndices
  GrassmannAbbreviations FiniteCoordinates Alternating AlternatingCoordinates
  CovectorProducts EuclideanCoordinateForms DualityMaps DivergenceUP DivergenceSealed
  DivergenceDerivative DivergenceDualityAlgebra ExteriorDifferentialUP ExteriorDifferentialSealed ExteriorDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [field_divergence_duality]: the original
    displayed equation d(D_p xi)=(-1)^(n-p)
    D_(p-1)(div xi), Federer 4.1.6,
    p. 354. Positive input degree is p+1;
    the actual preceding-degree partial graph is used. *)
Theorem field_divergence_duality (R:realType) (h2:(1+1:R)!=0) n p (hp:(p.+1<=n)%N)
    (NV:R_n R n->R) (NP:exterior_power (R_n R n) p.+1->R)
    (hNV:is_real_norm NV) (hNP:is_real_norm NP)
    (P:A_m (R_n R n) R^o (n-p.+1)->R) (hP:is_real_norm P)
    (U:R_n R n->Prop) (xi:R_n R n->exterior_power (R_n R n) p.+1) a b:
  let volume:=@omega_lambda R h2 (R_n R n) n (@euclidean_coordinate_form R n) n (Lambda_top n) in
  has_field_divergence h2 NV NP U xi a b->
  exists d:A_m (R_n R n) R^o (n-p.+1).+1,
    has_exterior_derivative NV P U (fun x=>D_p volume hp (xi x)) a d /\
    form_include d=(-1:R)^+(n-p.+1)*:
      form_include (D_p volume (leq_trans (leqnSn p) hp) b).
Proof.
move=>volume [L [hL hB]].
pose DP:=hom_of_linear (@D_p R (R_n R n) n volume p.+1 hp).
have hBound:norm_bounded_linear NP P DP.
  have hBasis:=finite_e_lambda_basis (@coordinate_basisP R n) h2 p.+1.
  have hOrdinal:=finite_ordinal_basis hBasis.
  exact:(norm_finite_linear_bounded hNP hP hOrdinal DP).
have hDiff:=norm_differential_postcompose hNV hL hBound.
exists (@ExteriorDifferential.value R h2 n R^o (n-p.+1) (hom_comp DP L)); split.
- exists (hom_comp DP L); split; first exact:hDiff. exact:ExteriorDifferential.laws.
- have hEqual:=divergence_value_unique (@Divergence.laws R h2 n p L) hB.
  rewrite -hEqual; exact:exterior_differential_duality_divergence.
Qed.
