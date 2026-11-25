(** Federer (1969), 4.1.25, p. 383: vector
    summands associated with one common m-plane lie
    on a single exterior line, and so does their
    sum. Reuse the original signed-sum scaling laws
    of 2.1.1(6), p. 52, and the previously proved
    finite multivector dual. No new vector-series
    construction or completeness premise is needed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP SeminormNormingFunctional
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  AlternatingForms AlternatingIsomorphism AlternatingPairing PairingLinear
  CurrentCoefficientNorms CurrentMultivectorDual MultivectorDualSealed
  ContinuousDualUP NumericalSum NumericalSumValues NumericalSumScale
  NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Section NumericalSumLine.
Variable R : realType.
Hypothesis h2 : ((1+1 : R) != 0)%R.
Variable I : choiceType.
Variables n m : nat.
Local Notation V := (exterior_power (R_n R n) m).
Local Notation A := (A_m (R_n R n) R^o m).
Local Notation M := (@current_vector_mass R h2 n m).
Local Notation hM := (@current_vector_mass_real_norm R h2 n m).
Variable C : set I.
Variable w : I -> V.

(** Source for [current_vector_numerical_sum_line]:
    the vector sum in Federer 4.1.25, p. 383,
    stays in the common line of its summands.
    Zero total and zero summands are permitted. The
    reference vector alone must be nonzero; no
    literal degree-zero simplicity claim is made. *)
Theorem current_vector_numerical_sum_line (tau eta : V) :
  tau != (0 : V)%R ->
  (forall x, C x -> exists c : R, w x = c *: tau) ->
  (forall a : A, numerical_sum C (fun x => (pairing (w x) a)%:E) =
    Some (pairing eta a)%:E) ->
  exists c : R, eta = c *: tau.
Proof.
move=> hTau hLine hSum.
have hPositive : (0 < M tau)%R.
  by rewrite (@real_norm_positive R V M hM.1 hM.2 tau) hTau.
have [ell [_ hNorming]] := seminorm_norming_functional hM.1 tau.
pose a0 : A := (M tau)^-1 *: hom_to_form (hom_of_linear ell).
have hUnit : pairing tau a0 = 1%R.
  change (pairing_right tau ((M tau)^-1 *: hom_to_form (hom_of_linear ell)) = 1%R).
  rewrite linearZ /= pairing_rightE /pairing hom_to_formK hom_of_linearE hNorming.
  change ((M tau)^-1 * M tau = 1)%R.
  exact: mulVf (lt0r_neq0 hPositive).
have hPoint (a : A) x : C x -> pairing (w x) a =
    (pairing tau a * pairing (w x) a0)%R.
  move=> hx; have [c ->] := hLine x hx.
  change (pairing_left a (c *: tau) = pairing tau a * pairing_left a0 (c *: tau))%R.
  rewrite !linearZ !pairing_leftE hUnit.
  change (c * pairing tau a = pairing tau a * (c * 1))%R.
  by rewrite mulr1 mulrC.
have hPairing (a : A) : pairing eta a = (pairing eta a0 * pairing tau a)%R.
  pose b := pairing tau a.
  have hScale : numerical_sum C (fun x => b%:E * (pairing (w x) a0)%:E) =
      Some (b * pairing eta a0)%:E.
    have [->|hNonzero] := eqVneq b 0%R.
    - rewrite mul0r.
      have hEqual := numerical_sum_ext
        (fun x (_ : C x) => mul0e ((pairing (w x) a0)%:E)).
      rewrite hEqual numerical_sum_nonnegative; last by move=> x _; exact: lexx.
      by rewrite (nonnegative_sum_zero (fun x (_ : C x) => erefl (0 : \bar R))).
    - by rewrite numerical_sum_scale // hSum /= -EFinM.
  have hEqual : numerical_sum C (fun x => (pairing (w x) a)%:E) =
      numerical_sum C (fun x => b%:E * (pairing (w x) a0)%:E).
    apply: numerical_sum_ext => x hx; by rewrite (hPoint a x hx) EFinM.
  have h := hSum a; rewrite hEqual hScale in h.
  injection h => hValue.
  by rewrite -hValue mulrC.
exists (pairing eta a0).
apply: (continuous_dual_injective (@current_multivector_continuous_dual R h2 n m)).
apply: hom_ext => a; rewrite !MultivectorDual.laws.
change (pairing eta a = pairing_left a ((pairing eta a0) *: tau)).
by rewrite linearZ pairing_leftE hPairing.
Qed.
End NumericalSumLine.
