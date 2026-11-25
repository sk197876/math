(** Federer (1969), 4.1.25, p. 383: existence of the
    finite-dimensional vector sum used in the fibre formula.
    Reuse the absolute-sum criterion and linearity from
    2.1.1(5)–(7), pp. 52–53, and the actual finite
    multivector dual from 4.1.7, p. 357. This is a
    supporting existence proof, not an extra summability
    premise on the original theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP RealFunctionalNormUP
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  AlternatingForms AlternatingPairing PairingLinear LinearBasis
  CurrentCoefficientNorms CurrentDualNorm CurrentVectorSpaces
  FiniteMultivectorDual MultivectorDualSealed ExtendedRealPartial
  NonnegativeSum NonnegativeSumSupport NonnegativeSumScale
  NumericalSum NumericalSumAbsolute NumericalSumValues
  NumericalSumAdd NumericalSumScale.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Section VectorNumericalSum.
Variable R : realType.
Hypothesis h2 : ((1+1 : R) != 0)%R.
Variable I : choiceType.
Variables n m : nat.
Local Notation V := (exterior_power (R_n R n) m).
Local Notation A := (A_m (R_n R n) R^o m).
Local Notation M := (@current_vector_mass R h2 n m).
Local Notation N := (@current_form_comass R h2 n m).
Variable C : set I.
Variable w : I -> V.

(** Source for [current_vector_pairing_sum_finite]:
    absolute convergence of every covector evaluation in
    the vector sum of Federer 4.1.25, p. 383,
    from 2.1.1(5), p. 52, and the mass/comass bound
    of 4.1.7, p. 357. *)
Theorem current_vector_pairing_sum_finite :
  nonnegative_sum C (fun x => (M (w x))%:E) < +oo ->
  forall a : A, exists r : R,
    numerical_sum C (fun x => (pairing (w x) a)%:E) = Some r%:E.
Proof.
move=> hFinite a.
apply: (@numerical_sum_finite_iff_absolute R I C
  (fun x => (pairing (w x) a)%:E)).2.
pose s := nonnegative_sum C (fun x => (M (w x))%:E).
have hNonnegative x : C x -> 0 <= (M (w x))%:E.
  move=> _; rewrite lee_fin.
  exact: real_seminorm_nonnegative (@current_vector_mass_real_norm R h2 n m).1 _.
have hS : s = (fine s)%:E.
  symmetry; apply: fineK; rewrite (ge0_fin_numE (nonnegative_sum_nonnegative _ _)).
  exact: hFinite.
have hBound : nonnegative_sum C (fun x => `|(pairing (w x) a)%:E|) <=
    (N a)%:E * s.
  rewrite /s -nonnegative_sum_scale //; last first.
  - exact: real_seminorm_nonnegative (@current_form_comass_real_norm R h2 n m).1 _.
  apply: nonnegative_sum_mono => x hx.
  rewrite abse_EFin -EFinM lee_fin mulrC.
  exact: real_functional_norm_bound (@current_mass_pairing_norm R h2 n m (w x)) a.
apply: le_lt_trans hBound _.
by rewrite hS -EFinM ltry.
Qed.

(** Source for [current_vector_numerical_sum_exists]:
    the actual vector sum in Federer 4.1.25,
    p. 383, exists whenever its mass sum is finite.
    Construct the scalar functional only inside this
    existence proof; represent it by the previously proved
    finite multivector dual. No coordinate construction
    is exposed as a definition of the sum. *)
Theorem current_vector_numerical_sum_exists :
  nonnegative_sum C (fun x => (M (w x))%:E) < +oo ->
  exists eta : V, forall a : A,
    numerical_sum C (fun x => (pairing (w x) a)%:E) =
      Some (pairing eta a)%:E.
Proof.
move=> hFinite.
have hExists := current_vector_pairing_sum_finite hFinite.
pose q (a : A) : R := projT1 (cid (hExists a)).
have hQ (a : A) : numerical_sum C (fun x => (pairing (w x) a)%:E) = Some (q a)%:E.
  exact: projT2 (cid (hExists a)).
have hScale (c : R) (a : A) :
    numerical_sum C (fun x => c%:E * (pairing (w x) a)%:E) =
      Some (c*q a)%:E.
  have [->|hNonzero] := eqVneq c 0%R.
  - rewrite mul0r.
    have hEqual := numerical_sum_ext
      (fun x (_ : C x) => mul0e ((pairing (w x) a)%:E)).
    rewrite hEqual numerical_sum_nonnegative; last by move=> x _; exact: lexx.
    by rewrite (nonnegative_sum_zero (fun x (_ : C x) => erefl (0 : \bar R))).
  - by rewrite numerical_sum_scale // hQ /= -EFinM.
have hLinear : forall (c : R) (a b : A), q (c *: a + b)%R = (c*q a+q b)%R.
  move=> c a b.
  have hAdd := (@numerical_sum_add R I C
    (fun x => c%:E * (pairing (w x) a)%:E)
    (fun x => (pairing (w x) b)%:E)
    (c*q a)%:E (q b)%:E (c*q a+q b)%:E
    (hScale c a) (hQ b) (erefl _)).2.
  have hPoint x : (pairing (w x) (c *: a + b))%:E =
      c%:E * (pairing (w x) a)%:E + (pairing (w x) b)%:E.
    change ((pairing_right (w x) (c *: a+b))%:E =
      c%:E * (pairing (w x) a)%:E + (pairing (w x) b)%:E).
    by rewrite linearP EFinD -EFinM.
  have hEqual := numerical_sum_ext (fun x (_ : C x) => hPoint x).
  have h := hQ (c *: a+b)%R; rewrite hEqual hAdd in h.
  injection h => hInjected; symmetry; exact: hInjected.
pose ell : Hom A R^o := @HomMap R A R^o q (introT (asboolP _) hLinear).
have [k [b hB]] := @current_vector_finite_basis R h2 n m.
have [eta hEta] := @finite_multivector_dual_surjective R (R_n R n) m
  'I_k b hB ell.
exists eta => a.
have hValue : pairing eta a = q a.
  have h := congr1 (fun L : Hom A R^o => L a) hEta.
  by rewrite MultivectorDual.laws in h.
by rewrite hValue; exact: hQ.
Qed.
End VectorNumericalSum.
