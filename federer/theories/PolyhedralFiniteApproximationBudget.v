(** Federer (1969), 4.1.23, p. 379:
    assemble finitely many approximated cells or simple
    summands with one common positive error budget.
    The mass costs remain the exact supplied
    costs, without replacing them by coordinate norms. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ModuleQuotient RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentMassSealed CurrentFlatNorm SmoothCompactSet
  PolyhedralCurrentAlgebra CurrentFlatFiniteSumBound CurrentMassFiniteSumBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section FiniteApproximationBudget.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Variable U : set (R_n R n).
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation Current := (@current_space R h2 n U hU m).
Variable K : smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation F := (@current_flat_norm R h2 n m U hU K).
Local Notation M := (@CurrentMass.value R h2 n m U hU).
Local Notation Poly := (@polyhedral_current_subspace R h2 n m U hU K).

(** Source for [polyhedral_finite_approximation_budget]:
    finitely many original cell approximations
    give the stated approximation of their
    sum, supporting the finite reductions in
    Federer 4.1.23, p. 379.
    The supplied component assertion is a
    supporting implication; the final construction
    supplies it for actual simple cells. *)
Theorem polyhedral_finite_approximation_budget
    (I : finType) (T : I -> Current) (cost : I -> R)
    (hApprox : forall i delta, 0<delta -> exists P : Current,
      Poly P /\ (F (T i-P)<=delta%:E)%E /\
        (M P<=(cost i+delta)%:E)%E)
    (epsilon : R) (hEpsilon : 0<epsilon) :
  exists P : Current, Poly P /\
    (F ((\sum_i T i)-P)<=epsilon%:E)%E /\
    (M P<=((\sum_i cost i)+epsilon)%:E)%E.
Proof.
pose count := (#|I|%:R : R).
have hCount : 0<=count by rewrite /count ler0n.
have hDenominator : 0<count+1.
  apply: (lt_le_trans (@ltr01 R)); by rewrite lerDr.
pose delta := epsilon/(count+1).
have hDelta : 0<delta := divr_gt0 hEpsilon hDenominator.
have hPieces i : exists P : Current, Poly P /\
    (F (T i-P)<=delta%:E)%E /\ (M P<=(cost i+delta)%:E)%E.
  exact: (@hApprox i delta hDelta).
have [P hP] := choice hPieces.
have hPoly : Poly (\sum_i P i).
  elim/big_rec: _=> [|i a hI hA]; first exact: subspace_zero.
  exact: subspace_add (hP i).1 hA.
have hBudget : delta*count<=epsilon.
  have hIncrease : delta*count<=delta*(count+1).
    have hCountOne : count<=count+1 by rewrite lerDl ler01.
    exact: (ler_wpM2l (ltW hDelta) hCountOne).
  have hEnd : delta*(count+1)=epsilon.
    by rewrite /delta divfK ?gt_eqF.
  by rewrite -hEnd.
have hFlat := @current_flat_norm_finite_sum_bound R h2 n m U hU K I
  (fun i => T i-P i) (fun _ => delta) (fun i => (hP i).2.1).
rewrite sumrB sumr_const cardT -mulr_natr -/count in hFlat.
have hMass := @current_mass_finite_sum_bound R h2 n m U hU I P
  (fun i => cost i+delta) (fun i => (hP i).2.2).
rewrite big_split sumr_const cardT -mulr_natr -/count in hMass.
exists (\sum_i P i); split; first exact: hPoly.
split.
- apply: (le_trans hFlat); rewrite lee_fin -cardT -/count; exact: hBudget.
- apply: (le_trans hMass); rewrite lee_fin lerD2l -cardT -/count; exact: hBudget.
Qed.
End FiniteApproximationBudget.
