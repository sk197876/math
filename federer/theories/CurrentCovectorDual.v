(** Federer (1969), 4.1.19, p. 377: forms with
    comass are the actual continuous dual of multivectors
    with mass. Reuse 4.1.7's opposite dual identification,
    Hahn–Banach norming and the inverse maps of 1.4.1.
    No coefficient-space construction is repeated. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP RealFunctionalNormUP
  ContinuousRealFunctional ContinuousDualUP GrassmannAbbreviations
  ExteriorGrading AlternatingForms AlternatingIsomorphism AlternatingPairing PairingLinear
  CurrentCoefficientNorms CurrentDualNorm CurrentMultivectorDual
  MultivectorDualSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section CurrentCovectorDual.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation V := (exterior_power X m).
Local Notation Y := (A_m X R^o m).
Local Notation MN := (@current_vector_mass R h2 n m).
Local Notation YN := (@current_form_comass R h2 n m).
Local Notation hMN := (@current_vector_mass_real_norm R h2 n m).
Local Notation hYN := (@current_form_comass_real_norm R h2 n m).
Local Notation oldEval := (@MultivectorDual.evaluation R X m).
Local Notation hOld := (@current_multivector_continuous_dual R h2 n m).

(** Source for [current_comass_mass_dual_norm]: the
    comass norm of the forms representing a flat
    cochain in Federer 4.1.19, p. 377, is
    the exact functional norm against multivector mass.
    The preceding mass duality and norming theorem
    give both sharp directions in every natural degree. *)
Theorem current_comass_mass_dual_norm (phi : Y) :
  is_real_functional_norm MN (pairing_left phi) (YN phi).
Proof.
have hPhi : 0 <= YN phi := real_seminorm_nonnegative hYN.1 phi.
constructor.
- exact: hPhi.
- move=> xi.
  have hBound := real_functional_norm_bound
    (@current_mass_pairing_norm R h2 n m xi) phi.
  rewrite pairing_leftE mulrC; exact: hBound.
- move=> c hNonnegative hCap.
  have [a [hContinuous [hUnit hNorm]]] :=
    @continuous_norming_real_functional R Y YN hYN phi.
  have [xi hXi] := continuous_dual_surjective hOld
    (a:=hom_of_linear a) hContinuous.
  have hMass : MN xi <= 1.
    apply: (real_functional_norm_least
      (continuous_dual_norm_laws hOld xi) ler01).
    move=> theta.
    rewrite hom_as_linearE hXi hom_of_linearE mul1r.
    exact: hUnit.
  have hValue : pairing xi phi = YN phi.
    have hEvaluation := congr1 (fun ell : Hom Y R^o => ell phi) hXi.
    rewrite (@MultivectorDual.laws R X m xi phi) hom_of_linearE in hEvaluation.
    exact: (eq_trans hEvaluation hNorm).
  have hEstimate := hCap xi.
  rewrite pairing_leftE hValue (ger0_norm hPhi) in hEstimate.
  have hOne := ler_wpM2l hNonnegative hMass.
  rewrite mulr1 in hOne.
  exact: (le_trans hEstimate hOne).
Qed.

(** Source for [current_covector_evaluation]: the actual
    form-to-functional map of 1.4.1, p. 17,
    in the coefficient dual used by Federer
    4.1.19, p. 377. It is the already
    specified original pairing, with its variance explicit. *)
Definition current_covector_evaluation : Hom Y (Hom V R^o) :=
  @HomMap R Y (Hom V R^o) (@form_to_hom R X R^o m)
    (introT (asboolP _) (@form_to_hom_linear R X R^o m)).

(** Source for [current_covector_dual_norm]: the
    coefficient dual norm in Federer 4.1.19,
    p. 377, on the literal evaluation map.
    Both mass and comass retain their degree-zero
    absolute-scalar convention from 4.1.7. *)
Theorem current_covector_dual_norm (phi : Y) :
  is_real_functional_norm MN
    (hom_as_linear (current_covector_evaluation phi)) (YN phi).
Proof. exact: current_comass_mass_dual_norm. Qed.

(** Source for [current_covector_continuous_dual]:
    the actual mass-normed multivectors have the
    original comass-normed forms as their full
    continuous dual, supporting representation in
    Federer 4.1.19, p. 377. The inverse
    maps of 1.4.1 and preceding dual norm
    laws supply the entire interface. *)
Theorem current_covector_continuous_dual :
  is_continuous_dual hMN current_covector_evaluation YN.
Proof.
constructor.
- move=> phi psi hEqual.
  apply: (can_inj (@form_to_homK R X R^o m)).
  exact: hEqual.
- move=> phi.
  apply: (@bounded_real_functional_continuous R V MN hMN
    (hom_as_linear (current_covector_evaluation phi)) (YN phi)).
  + exact: (real_functional_norm_nonnegative (current_covector_dual_norm phi)).
  + exact: (real_functional_norm_bound (current_covector_dual_norm phi)).
- move=> a _; exists (@hom_to_form R X R^o m a).
  exact: (@hom_to_formK R X R^o m a).
- exact: current_covector_dual_norm.
Qed.
End CurrentCovectorDual.
