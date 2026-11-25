(** Supporting Federer (1969), 3.4.8(5), p. 328:
    actual divided directional coefficients determine an
    analytic germ. Polarisation from 1.10.4, p. 46,
    determines each symmetric derivative; the original
    Taylor injectivity determines the actual germ. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  SymmetricForms HomogeneousPolynomialFunctions PolynomialDiagonalNorm AnalyticGermRing
  AnalyticGermJetsSealed AnalyticGermCoefficientForms AnalyticGermTaylorInjective
  AnalyticGermDirectionalCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_germ_directional_coefficients_injective]:
    equality of all actual divided diagonal coefficients
    gives equality of the original analytic germs,
    supporting 3.4.8(5), p. 328, from 1.10.4,
    p. 46, and 3.4.5, p. 319. *)
Theorem analytic_germ_directional_coefficients_injective (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) a
  (alpha beta:@analytic_germ_ring R X NX hNX a):
  (forall k v,@analytic_germ_directional_coefficient R X NX hNX a k alpha v =
    @analytic_germ_directional_coefficient R X NX hNX a k beta v) ->alpha = beta.
Proof.
move=>hEqual.
have [phi [hPhi _]]:=@analytic_germ_coefficient_forms_exists R X NX hNX a alpha.
have [psi [hPsi _]]:=@analytic_germ_coefficient_forms_exists R X NX hNX a beta.
apply:(@analytic_germ_jets_injective R X NX hNX a alpha beta)=>k.
have hForm:phi k = psi k.
  apply:(@sform_polynomial_injective R X R^o k (@pchar_num R)).
  apply:funext=>v;rewrite !sform_polynomial_diagonal_value hPhi hPsi.
  have hTuple:[ffun i=>tnth [tuple v | j<k] i] = [ffun _:'I_k=>v].
    by apply/ffunP=>i;rewrite !ffunE tnth_mktuple.
  rewrite hTuple;exact:hEqual k v.
apply:(continuous_multilinear_extensional (@ContinuousMultilinear.laws R k X R^o NX
  (fun z=>`|z|) hNX (@scalar_absolute_value_norm R)))=>u.
have hh:=congr1 (fun F:S_m X R^o k=>F [tuple u i | i<k]) hForm.
rewrite hPhi hPsi in hh.
have hTuple:[ffun i=>tnth [tuple u j | j<k] i] = u.
  by apply/ffunP=>i;rewrite !ffunE tnth_mktuple.
by rewrite hTuple in hh.
Qed.
