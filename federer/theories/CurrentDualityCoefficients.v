(** Federer (1969), 4.1.7, p. 356:
    the original complementary-degree duality in
    the current diagram. Reuse the two inverse
    maps of 1.5.2 and the signed divergence
    identity proved in 4.1.6, p. 354. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import ExteriorDeterminant FiniteExteriorPowers AlternatingProduct AlternatingSum ComassWedgeSymmetry ScalarCoefficients BoundedHom HomogeneousHom GradedComponents Hom RealNormUP NormDifferentialUP GrassmannAbbreviations
  FiniteCoordinates EuclideanCoordinateForms ExteriorGrading ExteriorIndices AlternatingForms
  AlternatingPairing ExteriorHomogeneousProducts CovectorProducts DualityMaps DualityBasis
  DualityIsomorphism DivergenceSealed DivergenceDualityAlgebra ExteriorDifferentialSealed
  CurrentCoefficientNorms CurrentCoefficientCompleteness CurrentVectorSpaces NormFiniteLinearBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentDualityCoefficients.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n p:nat.
Local Notation X := (R_n R n).
Local Notation e := (@coordinate_basis R n).
Local Notation omega := (@euclidean_coordinate_form R n).
Local Notation volume := (@omega_lambda R h2 X n omega n (Lambda_top n)).
Hypothesis hp:(p<=n)%N.

(** Source for [current_duality_lower_coefficient]:
    the original D_p in actual complementary
    degrees, supporting the diagram in Federer
    4.1.7, p. 356. *)
Definition current_duality_lower_coefficient:Hom (exterior_power X p) (A_m X R^o (n-p)):=
  hom_of_linear (@D_p R X n volume p hp).

(** Source for [current_duality_upper_coefficient]:
    the original D^(n-p), with only the
    equality n-(n-p)=p transported, supporting
    Federer 4.1.7, p. 356. The
    map is the already proved D_inverse. *)
Definition current_duality_upper_coefficient:Hom (A_m X R^o (n-p)) (exterior_power X p):=
  hom_of_linear (@D_inverse R h2 X n e p hp).

(** Source for [current_duality_lower_upper_cancel]:
    the original complementary maps are inverse,
    supporting Federer 4.1.7, p. 356,
    by 1.5.2, p. 22. *)
Lemma current_duality_lower_upper_cancel:cancel current_duality_lower_coefficient current_duality_upper_coefficient.
Proof.
exact:(@D_pK R h2 X n e omega (@coordinate_basisP R n) (@euclidean_coordinate_form_dual R n) p hp).
Qed.

(** Source for [current_duality_upper_lower_cancel]:
    the opposite original inverse equality,
    supporting Federer 4.1.7, p. 356. *)
Lemma current_duality_upper_lower_cancel:cancel current_duality_upper_coefficient current_duality_lower_coefficient.
Proof.
exact:(@D_inverseK R h2 X n e omega (@coordinate_basisP R n) (@euclidean_coordinate_form_dual R n) p hp).
Qed.

(** Source for [current_duality_lower_bounded]:
    the original lower duality is bounded
    for mass and comass, supporting the
    actual smooth diagram in Federer 4.1.7,
    p. 356, by finite-dimensional 3.1.1. *)
Lemma current_duality_lower_bounded:
  norm_bounded_linear (@current_vector_mass R h2 n p) (@current_form_comass R h2 n (n-p))
    current_duality_lower_coefficient.
Proof.
have [d [b hb]]:=@current_vector_finite_basis R h2 n p.
exact:(@norm_finite_linear_bounded R (exterior_power X p) (A_m X R^o (n-p))
  (@current_vector_mass R h2 n p) (@current_form_comass R h2 n (n-p))
  (@current_vector_mass_real_norm R h2 n p) (@current_form_comass_real_norm R h2 n (n-p))
  d b hb current_duality_lower_coefficient).
Qed.

(** Source for [current_duality_upper_bounded]:
    the original inverse duality is bounded
    for comass and mass, supporting Federer
    4.1.7, p. 356. *)
Lemma current_duality_upper_bounded:
  norm_bounded_linear (@current_form_comass R h2 n (n-p)) (@current_vector_mass R h2 n p)
    current_duality_upper_coefficient.
Proof.
have [d [b hb]]:=@current_form_finite_basis R h2 n (n-p).
exact:(@norm_finite_linear_bounded R (A_m X R^o (n-p)) (exterior_power X p)
  (@current_form_comass R h2 n (n-p)) (@current_vector_mass R h2 n p)
  (@current_form_comass_real_norm R h2 n (n-p)) (@current_vector_mass_real_norm R h2 n p)
  d b hb current_duality_upper_coefficient).
Qed.

(** Source for [current_duality_upper_pairing]:
    <D^(n-p) phi,psi>=<e_top,phi wedge psi>,
    the displayed integral integrand identity in
    Federer 4.1.7, p. 356. *)
Lemma current_duality_upper_pairing phi (psi:A_m X R^o p):
  pairing (current_duality_upper_coefficient phi) psi=
  alternating_wedge h2 (scalar_bilinear R) (form_include phi) (form_include psi)
    (component_val (e_lambda e (val (Lambda_top n)))).
Proof. exact:D_inverse_evaluation. Qed.
End CurrentDualityCoefficients.

(** Source for [current_upper_duality_divergence_algebra]:
    div(D^(n-p) phi)=(-1)^(n-p)
    D^(n-p+1)(d phi), the left square
    in Federer 4.1.7, p. 356. The
    equality here applies to actual first
    differentials, with every degree cast explicit. *)
Theorem current_upper_duality_divergence_algebra (R:realType) (h2:(1+1:R)!=0)
    n p (hp:(p.+1<=n)%N) (L:Hom (R_n R n) (A_m (R_n R n) R^o (n-p.+1))):
  @Divergence.value R h2 n p
    (hom_comp (@current_duality_upper_coefficient R h2 n p.+1 hp) L)=
  (-1:R)^+(n-p.+1)*:
    @current_duality_upper_coefficient R h2 n p (leq_trans (leqnSn p) hp)
      (form_reindex (subnSK hp) (@ExteriorDifferential.value R h2 n R^o (n-p.+1) L)).
Proof.
pose X:=R_n R n.
pose e:=@coordinate_basis R n.
pose omega:=@euclidean_coordinate_form R n.
pose volume:=@omega_lambda R h2 X n omega n (Lambda_top n).
pose lower:=@current_duality_lower_coefficient R h2 n p.+1 hp.
pose upper:=@current_duality_upper_coefficient R h2 n p.+1 hp.
pose hp0:=leq_trans (leqnSn p) hp.
pose upper0:=@current_duality_upper_coefficient R h2 n p hp0.
have hCancel:hom_comp lower (hom_comp upper L)=L.
  apply:hom_ext=>x;rewrite !hom_compE.
  exact:current_duality_upper_lower_cancel.
have hAlgebra:=@exterior_differential_duality_divergence R h2 n p hp (hom_comp upper L).
change (form_include (@ExteriorDifferential.value R h2 n R^o (n-p.+1)
    (hom_comp lower (hom_comp upper L)))=
  (-1:R)^+(n-p.+1)*:form_include
    (@current_duality_lower_coefficient R h2 n p hp0 (@Divergence.value R h2 n p (hom_comp upper L))))
  in hAlgebra.
rewrite hCancel in hAlgebra.
have hForm:form_reindex (subnSK hp) (@ExteriorDifferential.value R h2 n R^o (n-p.+1) L)=
    (-1:R)^+(n-p.+1)*:
      @current_duality_lower_coefficient R h2 n p hp0 (@Divergence.value R h2 n p (hom_comp upper L)).
  apply:(can_inj (@form_includeK R X R^o (n-p))).
  rewrite form_reindex_include linearZ;exact:hAlgebra.
have hValue:=congr1 upper0 hForm.
have hCancel0:upper0 (@current_duality_lower_coefficient R h2 n p hp0
    (@Divergence.value R h2 n p (hom_comp upper L)))=
    @Divergence.value R h2 n p (hom_comp upper L).
  exact:(@current_duality_lower_upper_cancel R h2 n p hp0
    (@Divergence.value R h2 n p (hom_comp upper L))).
have hScale:upper0 ((-1:R)^+(n-p.+1)*:
    @current_duality_lower_coefficient R h2 n p hp0
      (@Divergence.value R h2 n p (hom_comp upper L)))=
    (-1:R)^+(n-p.+1)*:upper0
      (@current_duality_lower_coefficient R h2 n p hp0
        (@Divergence.value R h2 n p (hom_comp upper L))).
  exact:(linearZZ (hom_as_linear upper0) _ _).
have hMapped:=eq_trans hValue (eq_trans hScale
  (congr1 (fun z:exterior_power X p=>(-1:R)^+(n-p.+1)*:z) hCancel0)).
have hSigned:=congr1 (fun z:exterior_power X p=>(-1:R)^+(n-p.+1)*:z) hMapped.
have hSquare (z:exterior_power X p):
    (-1:R)^+(n-p.+1)*:((-1:R)^+(n-p.+1)*:z)=z.
  by rewrite scalerA -exprMn mulrNN mul1r expr1n scale1r.
exact:(esym (eq_trans hSigned (hSquare _))).
Qed.
