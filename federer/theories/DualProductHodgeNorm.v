(** Federer (1969), 1.7.11, p. 36: supporting conversion of the dual product
    from 1.6.5 to the wedge of Hodge duals. Signs from 1.7.8 disappear upon
    taking norms. This allows reuse of the product-space identity already
    proved in 1.6.5. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm InnerPolarity InnerExterior
  ExteriorNorm ExteriorCovectorInner ExteriorGrading ExteriorHomogeneousProducts
  AlternatingCoordinates AlternatingAlgebra AlternatingUnit ScalarCoefficients
  LinearBasis OrthonormalFamilies FiniteExteriorPowers CovectorProducts
  DualityMaps HodgeMaps HodgeSignedDuality HodgeAlgebraCompatibility
  UpperDualityNorm Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Norm.
Variable R : rcfType.
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

(** Source for [dual_product_hodge_norm]: Federer 1.7.11,
    p. 36, supporting norm identity: upper duality of the wedge
    of the two lower duals has the same norm as the wedge of
    their Hodge duals. No simplicity or unit hypothesis on the
    inputs is needed for this algebraic and metric reduction. *)
Theorem dual_product_hodge_norm k l (hk : (k <= n)%N)
    (hl : (l <= n)%N) (hb : ((n-k)+(n-l) <= n)%N)
    (x : exterior_power V k) (y : exterior_power V l) :
  exterior_norm h2 hB
    (D_upper h2 E hb (form_wedge h2 (scalar_bilinear R)
      (D_p Omega hk x) (D_p Omega hl y))) =
  exterior_norm h2 hB
    (exterior_product (hodge_vector h2 hB E hk x)
      (hodge_vector h2 hB E hl y)).
Proof.
have hE : exterior_norm h2 hB E = 1.
  exact: orthonormal_product_unit_norm.
rewrite (@upper_duality_norm R h2 V B hB n e he E hE).
rewrite -(@inner_exterior_form_norm R h2 V B hB n e he ((n-k)+(n-l)))
  inner_exterior_form_wedge !(@hodge_polarity_signed_duality R h2 V B hB n e he ho)
  (bilZl (form_wedge_bilinear h2 V (scalar_bilinear R) (n-k) (n-l)))
  (bilZr (form_wedge_bilinear h2 V (scalar_bilinear R) (n-k) (n-l))).
by rewrite /exterior_covector_norm !inner_normZ !normrX !normrN !normr1 !expr1n !mul1r.
Qed.
End Norm.
