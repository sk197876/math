(** Federer (1969), 4.1.12, p. 368: the
    original interval-series boundary has infinite mass.
    The actual bounded endpoint tests have
    arbitrarily large actions. Use original testwise
    series convergence and the original mass supremum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate AlternatingForms AlternatingZero
  CurrentSpaces CurrentBoundary CurrentMassSealed CurrentMassBasic CurrentGlobalComassSealed CurrentGlobalComassBound CurrentZeroCovectorMaps
  CurrentWeakLimitOperations DyadicCurrentEndpointArithmetic DyadicIntervalCurrentUP DyadicIntervalCurrentSealed DyadicIntervalCurrentLaws
  DyadicIntervalBoundaryPrefix DyadicIntervalBoundaryTest FinitePrefixSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section DyadicIntervalBoundaryMass.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation S := (@DyadicIntervalCurrent.value R h2).
Local Notation T := (@dyadic_interval_boundary R h2).
Local Notation B := (@current_boundary R h2 1%N 0%N Full hFull).
Local Notation prefix := (@dyadic_interval_current_prefix R h2).
Local Notation action := (@current_value R h2 1%N Full hFull 0%N).
Local Notation value := (@current_test_value R h2 1%N Full hFull 0%N).
Local Notation M := (@CurrentMass.value R h2 1%N 0%N Full hFull).

(** Source for [dyadic_interval_boundary_arbitrary_mass_lower]:
    the original boundary admits a unit-comass
    test with value N for every natural
    N, supporting M(T)=infinity in Federer
    4.1.12, p. 368. *)
Theorem dyadic_interval_boundary_arbitrary_mass_lower N:
  (((N%:R:R)%:E)<=M T)%E.
Proof.
have[gamma [hRange [hLeft hRight]]]:=@dyadic_interval_boundary_test_exists R h2 N.
have hPrefix L:(N<=L)%N->action (B (prefix L)) gamma=(N%:R:R).
  move=>hNL;rewrite dyadic_interval_boundary_prefix_value.
  have hTerm j:zero_form_value (value gamma
      (euclidean_one_embed (dyadic_current_right_endpoint R j)))-
      zero_form_value (value gamma (euclidean_one_embed (dyadic_current_left_endpoint R j)))=
      (if (j<N)%N then 1 else 0).
    by rewrite hLeft hRight zero_formK (linear0 (@zero_form_value R X R^o)) subr0.
  have hSum: \sum_(j<L) (zero_form_value (value gamma
      (euclidean_one_embed (dyadic_current_right_endpoint R j)))-
      zero_form_value (value gamma (euclidean_one_embed (dyadic_current_left_endpoint R j))))=
      \sum_(j<L) (if (j<N)%N then (1:R) else 0).
    apply:eq_bigr=>j _;exact:hTerm j.
  rewrite hSum.
  have hZero j:(N<=j)%N->(if (j<N)%N then (1:R) else 0)=0.
    by move=>hNJ;rewrite (leq_gtF hNJ).
  rewrite -(@finite_prefix_sum_extend R^o (fun j=>if (j<N)%N then (1:R) else 0) N L hNL hZero).
  have hOnes: \sum_(j<N) (if (j<N)%N then (1:R) else 0)=\sum_(j<N) (1:R).
    apply:eq_bigr=>j _;by rewrite ltn_ord.
  by rewrite hOnes sumr_const card_ord -mulr_natl mulr1.
have hWeak:=@current_weak_limit_boundary R h2 1%N 0%N Full hFull prefix S
  (@DyadicIntervalCurrent.laws R h2).
have hValue:action T gamma=(N%:R:R):=
  @current_weak_limit_eventual_value R h2 1%N 0%N Full hFull
    (fun k=>B (prefix k)) T gamma (N%:R:R) N hWeak hPrefix.
have hTest:(@CurrentGlobalComass.value R h2 1%N 0%N Full (value gamma)<=1)%E.
  apply:(@current_global_comass_bound R h2 1%N 0%N Full (value gamma) 1).2=>x _.
  rewrite current_zero_form_coefficient_norm (ger0_norm (andP (hRange x)).1).
  exact:(andP (hRange x)).2.
have hMass:=@current_mass_unit_test_upper R h2 1%N 0%N Full hFull T gamma hTest.
by rewrite hValue in hMass.
Qed.

(** Source for [dyadic_interval_boundary_infinite_mass]:
    the actual current T printed in
    Federer 4.1.12, p. 368, has
    infinite original mass. *)
Theorem dyadic_interval_boundary_infinite_mass:M T=(+oo)%E.
Proof.
have hNotFinite:~(M T< +oo)%E.
  move=>hFinite.
  have[b [hb hMass]]:=@current_finite_mass_value R h2 1%N 0%N Full hFull T hFinite.
  pose N:=Num.bound `|b|.
  have hArch:`|b|<(N%:R:R):=archi_boundP (normr_ge0 b).
  have hStrict:b<(N%:R:R):=le_lt_trans (ler_norm b) hArch.
  have hLower:=dyadic_interval_boundary_arbitrary_mass_lower N.
  rewrite hMass lee_fin in hLower.
  by have:=le_lt_trans hLower hStrict;rewrite ltxx.
have hTop:((+oo)%E<=M T)%E by rewrite leNgt;exact/negP.
apply/eqP;by rewrite eq_le leey hTop.
Qed.
End DyadicIntervalBoundaryMass.
