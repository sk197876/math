(** Federer (1969), 4.1.25, p. 383: bound
    the mass of the actual vector fibre sum by
    the sum of the individual masses. Reuse the
    signed-sum comparison of 2.1.1(8), p. 53,
    and the sharp mass/comass duality of 4.1.7,
    p. 357. Empty sums and degree zero remain. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP RealFunctionalNormUP
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  AlternatingForms AlternatingPairing PairingLinear CurrentCoefficientNorms
  CurrentDualNorm NonnegativeSum NonnegativeSumScale
  NumericalSum NumericalSumValues NumericalSumOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Section VectorSumMass.
Variable R : realType.
Hypothesis h2 : ((1+1 : R) != 0)%R.
Variable I : choiceType.
Variables n m : nat.
Local Notation V := (exterior_power (R_n R n) m).
Local Notation A := (A_m (R_n R n) R^o m).
Local Notation M := (@current_vector_mass R h2 n m).
Local Notation N := (@current_form_comass R h2 n m).
Local Notation hM := (@current_vector_mass_real_norm R h2 n m).
Local Notation hN := (@current_form_comass_real_norm R h2 n m).
Variable C : set I.
Variable w : I -> V.

(** Source for [current_vector_numerical_sum_mass_bound]:
    the triangle bound for the literal vector
    fibre sum in Federer 4.1.25, p. 383.
    The given evaluations characterize the actual vector
    sum; the real size on the right is used
    only after its finiteness has been proved. *)
Theorem current_vector_numerical_sum_mass_bound (eta : V) :
  nonnegative_sum C (fun x => (M (w x))%:E) < +oo ->
  (forall a : A, numerical_sum C (fun x => (pairing (w x) a)%:E) =
    Some (pairing eta a)%:E) ->
  (M eta <= fine (nonnegative_sum C (fun x => (M (w x))%:E)))%R.
Proof.
move=> hFinite hSum.
pose s := nonnegative_sum C (fun x => (M (w x))%:E).
have hSNonnegative : 0 <= s := nonnegative_sum_nonnegative _ _.
have hSFinite : s \is a fin_num.
  by rewrite (ge0_fin_numE hSNonnegative).
have hSValue : s = (fine s)%:E by symmetry; exact: fineK.
have hRealNonnegative : (0 <= fine s)%R.
  by move: hSNonnegative; rewrite hSValue lee_fin.
have hUpper (a : A) : (pairing eta a <= N a * fine s)%R.
  pose g x := (N a)%:E * (M (w x))%:E.
  have hMNonnegative x : C x -> 0 <= (M (w x))%:E.
    move=> _; rewrite lee_fin; exact: real_seminorm_nonnegative hM.1 _.
  have hANonnegative : (0 <= N a)%R := real_seminorm_nonnegative hN.1 a.
  have hGNonnegative x : C x -> 0 <= g x.
    move=> hx; apply: mule_ge0; first by rewrite lee_fin.
    exact: hMNonnegative x hx.
  have hG : numerical_sum C g = Some (N a*fine s)%:E.
    rewrite numerical_sum_nonnegative // /g
      (nonnegative_sum_scale hANonnegative hMNonnegative) -/s hSValue -EFinM.
    reflexivity.
  have hTerm x : C x -> (pairing (w x) a)%:E <= g x.
    move=> hx; rewrite /g -EFinM lee_fin mulrC.
    exact: le_trans (ler_norm _)
      (real_functional_norm_bound (@current_mass_pairing_norm R h2 n m (w x)) a).
  have hBound := numerical_sum_values_mono hTerm (hSum a) hG.
  by move: hBound; rewrite lee_fin.
apply: (real_functional_norm_least (@current_mass_pairing_norm R h2 n m eta) hRealNonnegative)
  => a.
rewrite mulrC; change (`|pairing eta a| <= N a*fine s)%R.
rewrite ler_norml; apply/andP; split; last exact: hUpper.
have hNegative := hUpper ((-a)%R).
change (is_true (pairing_right eta (-a) <= N (-a)*fine s)%R) in hNegative.
rewrite linearN /= (real_seminorm_negate hN.1) in hNegative.
by rewrite lerNl; exact: hNegative.
Qed.
End VectorSumMass.
