(** Federer (1969), 4.1.7, p. 358, used in
    4.1.12, p. 368: convergence in original
    mass implies convergence on every original compact
    test. The proved positive test bound and finite
    homogeneous mass estimate supply the implication. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal ring.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentPointEvaluation CurrentMassSealed
  CurrentMassBasic CurrentMassTestBound CurrentWeakSequenceLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_mass_convergence_is_weak]: the
    original mass topology is stronger than convergence
    on each test, supporting the mass-closure assertion
    of Federer 4.1.12, p. 368. No common
    compact support or representation premise is needed. *)
Theorem current_mass_convergence_is_weak (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (u:nat->@current_space R h2 n U hU m) (T:@current_space R h2 n U hU m):
  (forall epsilon:R,0<epsilon->exists k,forall L,(k<=L)%N->
    (@CurrentMass.value R h2 n m U hU (T-u L)<epsilon%:E)%E)->
  @is_current_weak_sequence_limit R h2 n m U hU u T.
Proof.
move=>hMass phi epsilon hEpsilon.
have[a [ha hPhi]]:=@current_test_positive_comass_bound R h2 n m U hU phi.
have hDelta:0<epsilon/a by rewrite divr_gt0.
have[k hk]:=hMass (epsilon/a) hDelta.
exists k=>L hKL.
have hFinite:(@CurrentMass.value R h2 n m U hU (T-u L)< +oo)%E:=
  lt_trans (hk L hKL) (ltry _).
have[b [hb hValue]]:=@current_finite_mass_value R h2 n m U hU (T-u L) hFinite.
have hB:b<epsilon/a by have h:=hk L hKL;by rewrite hValue lte_fin in h.
have hBound:=@current_finite_mass_test_bound R h2 n m U hU (T-u L) phi a b hValue ha hPhi.
pose E:=@current_point_evaluation R h2 n m U hU phi.
have hDifference:@current_value R h2 n U hU m (T-u L) phi=
    -(@current_value R h2 n U hU m (u L) phi-@current_value R h2 n U hU m T phi).
  change (E (T-u L)= -(E (u L)-E T));rewrite (linB (hom_linear E));ring.
rewrite hDifference normrN in hBound.
apply:(le_lt_trans hBound).
have hStrict:a*b<a*(epsilon/a) by rewrite (ltr_pM2l ha).
have hEndpoint:a*(epsilon/a)=epsilon by rewrite mulrC divfK ?gt_eqF.
by rewrite hEndpoint in hStrict.
Qed.
