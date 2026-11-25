(** Federer (1969), 3.4.12, p. 339: actual complex mixed
    Taylor coefficients exist and are unique. The original germ
    forms remain opaque; their laws supply the only representatives. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom ScalarRestriction ComplexScalarSealed ComplexNormUP
  SymmetricForms PolynomialTaylorTerms HomogeneousPolynomialFunctions
  HolomorphicGermUP HolomorphicGermFormsUP HolomorphicGermFormsSealed
  ComplexWeierstrassCoefficientUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [complex_weierstrass_split_coefficients_exist]: the
    original double sequence in 3.4.6, p. 322, over the
    complex field as required in 3.4.12, p. 339. *)
Theorem complex_weierstrass_split_coefficients_exist (R:realType)
    (X K:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:is_complex_norm NX)
    (alpha:holomorphic_germ_space (complex_norm_real hNX) (0:X))
    (v:X) (inclusion:Hom K X):
  exists C:nat->nat->K->ComplexScalars.C R,forall i j,
    is_complex_weierstrass_split_coefficient hNX alpha v inclusion i j (C i j).
Proof.
pose F m:=@HolomorphicGermForms.value R X NX hNX 0 m alpha.
exists (fun i j z=>sform_polynomial_value (symmetric_taylor_term j (F (i+j)%N) v) (inclusion z)).
move=>i j G hG z.
have hEqual:G=F (i+j)%N.
  apply:sform_ext=>t;rewrite hG.
  exact:esym (@HolomorphicGermForms.laws R X NX hNX 0 (i+j)%N alpha t).
by rewrite hEqual.
Qed.

(** Source for [complex_weierstrass_split_coefficient_unique]: the
    actual original germ determines every mixed coefficient uniquely,
    3.4.12, p. 339, extending 3.4.6, pp. 322–323. *)
Theorem complex_weierstrass_split_coefficient_unique (R:realType)
    (X K:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:is_complex_norm NX)
    (alpha:holomorphic_germ_space (complex_norm_real hNX) (0:X))
    (v:X) (inclusion:Hom K X) i j (C D:K->ComplexScalars.C R):
  is_complex_weierstrass_split_coefficient hNX alpha v inclusion i j C ->
  is_complex_weierstrass_split_coefficient hNX alpha v inclusion i j D ->C=1 D.
Proof.
move=>hC hD z.
pose F:=@HolomorphicGermForms.value R X NX hNX 0 (i+j)%N alpha.
have hF:=@HolomorphicGermForms.laws R X NX hNX 0 (i+j)%N alpha.
by rewrite (hC F hF z) (hD F hF z).
Qed.
