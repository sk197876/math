(** Federer (1969), 4.1.20, p. 378: the top-degree
    density currents with null support vanish. The implicit
    zero-mass step uses the original mass definition of 4.1.7,
    p. 358, and its bound on each original compact test. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentEvaluation CurrentMassSealed CurrentMassTestBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_zero_mass]: zero original mass forces
    every original test action to vanish, the implicit mass
    step in Federer 4.1.20, p. 378, using 4.1.7, p. 358.
    No compact support or representation hypothesis is needed. *)
Theorem current_zero_mass (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m):
  @CurrentMass.value R h2 n m U hU T=0->T=0.
Proof.
move=>hMass;apply:(@current_values_extensional R h2 n m U hU)=>psi.
have[a [hA hBound]]:=@current_test_positive_comass_bound R h2 n m U hU psi.
have hFinal:=@current_finite_mass_test_bound R h2 n m U hU T psi a 0
  hMass hA hBound.
rewrite mulr0 in hFinal.
have hValue:@current_value R h2 n U hU m T psi=0.
  apply/eqP;by rewrite -normr_eq0 eq_le hFinal normr_ge0.
by rewrite hValue linear0 hom_zeroE.
Qed.
