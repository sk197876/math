(** Draft supporting Federer (1969), 4.1.14, p. 370:
    an N-bounded weak limit with a fixed compact support
    is normal. The separate sharp current and boundary bounds
    also survive, even when support and mass bounds hold only
    eventually. Reuse the preceding mass lower-limit and
    boundary-continuity laws. This plaintext draft has
    not been compiled or registered. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct CurrentSpaces CurrentBoundary SmoothCompactSet
  CurrentSupportGeometry CurrentMassSealed CurrentMassBasic
  CurrentFiniteMassRepresentation NormalCurrentsUP
  CurrentWeakSequenceLimit CurrentWeakLimitOperations
  CurrentWeakEventualCompactSupport CurrentMassWeakLowerLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section NormalCurrentWeakClosedBound.
Variable R : realType.
Hypothesis h2 : (1 + 1 : R) != 0.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation NX :=
  (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX :=
  (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation C d := (@current_space R h2 n U hU d).
Local Notation M d := (@CurrentMass.value R h2 n d U hU).
Variable K : smooth_compact_set hNX U.
Local Notation bd d := (@current_boundary R h2 n d U hU).
Local Notation supported d := (@normal_currents_supported_in R h2 n U hU d K).

(** Source for [normal_current_weak_closed_zero_mass_bound]:
    the zero-degree normal image limit retains its original
    current mass bound and compact index in Federer 4.1.14,
    p. 370. Support and mass bounds need hold only
    eventually, with independent thresholds. No boundary of
    negative degree or representation premise is introduced. *)
Theorem normal_current_weak_closed_zero_mass_bound
    (u:nat->C 0%N) (T:C 0%N) (a: \bar R):
  @is_current_weak_sequence_limit R h2 n 0%N U hU u T->
  (exists k,forall L,(k<=L)%N->
    @current_support R h2 n U hU 0%N (u L) `<=` smooth_compact_carrier K)->
  (a< +oo)%E->
  (exists k,forall L,(k<=L)%N->(M 0%N (u L)<=a)%E)->
  supported 0%N T /\(M 0%N T<=a)%E.
Proof.
move=>hWeak [kSupport hSupport] hFinite [kMass hBound].
have hTSupport:=@current_weak_limit_eventual_support_compact R h2 n 0%N
  U hU K u T kSupport hWeak hSupport.
have hMass:=@current_mass_weak_closed_bound R h2 n 0%N U hU
  u T a kMass hWeak hBound.
have hRepresented:=@current_finite_mass_representation R h2 n 0%N U hU T
  (le_lt_trans hMass hFinite).
split;last exact:hMass.
split;last exact:hTSupport.
split;last exact:(@current_support_compact_bound R h2 n 0%N U hU K T hTSupport).
split;first exact:hRepresented.
by [].
Qed.

(** Source for [normal_current_weak_closed_positive_mass_bounds]:
    the positive-degree normal image limit retains each original
    sharp current and boundary mass bound and the same compact
    target index, supporting Federer 4.1.14, p. 370.
    Finite mass of both limit currents is derived from the
    bounds. Neither limit representability nor normality of the
    finite initial approximation prefix is assumed. *)
Theorem normal_current_weak_closed_positive_mass_bounds d
    (u:nat->C d.+1) (T:C d.+1) (a b: \bar R):
  @is_current_weak_sequence_limit R h2 n d.+1 U hU u T->
  (exists k,forall L,(k<=L)%N->
    @current_support R h2 n U hU d.+1 (u L) `<=` smooth_compact_carrier K)->
  (a< +oo)%E->(b< +oo)%E->
  (exists k,forall L,(k<=L)%N->(M d.+1 (u L)<=a)%E)->
  (exists k,forall L,(k<=L)%N->(M d (bd d (u L))<=b)%E)->
  supported d.+1 T /\(M d.+1 T<=a)%E /\(M d (bd d T)<=b)%E.
Proof.
move=>hWeak [kSupport hSupport] hAFinite hBFinite
  [kMass hBound] [kBoundary hBoundaryBound].
have hTSupport:=@current_weak_limit_eventual_support_compact R h2 n d.+1
  U hU K u T kSupport hWeak hSupport.
have hMass:=@current_mass_weak_closed_bound R h2 n d.+1 U hU
  u T a kMass hWeak hBound.
have hBoundaryWeak:=@current_weak_limit_boundary R h2 n d U hU u T hWeak.
have hBoundaryMass:=@current_mass_weak_closed_bound R h2 n d U hU
  (fun k=>bd d (u k)) (bd d T) b kBoundary hBoundaryWeak hBoundaryBound.
have hRepresented:=@current_finite_mass_representation R h2 n d.+1 U hU T
  (le_lt_trans hMass hAFinite).
have hBoundaryRepresented:=@current_finite_mass_representation R h2 n d U hU
  (bd d T) (le_lt_trans hBoundaryMass hBFinite).
split.
- split;last exact:hTSupport.
  split;last exact:(@current_support_compact_bound R h2 n d.+1 U hU K T hTSupport).
  split;first exact:hRepresented.
  exact:hBoundaryRepresented.
- by split.
Qed.

(** Source for [normal_current_weak_closed_positive_sum_bound]:
    the sum of the separately proved original bounds bounds
    N of the positive-degree limit, supporting 4.1.14,
    p. 370, by the definition in 4.1.7, p. 358.
    This is a proved sum bound; no same-cap N-closed-ball
    assertion is inferred from two separate same-cap bounds. *)
Corollary normal_current_weak_closed_positive_sum_bound d
    (u:nat->C d.+1) (T:C d.+1) (a b: \bar R):
  @is_current_weak_sequence_limit R h2 n d.+1 U hU u T->
  (exists k,forall L,(k<=L)%N->
    @current_support R h2 n U hU d.+1 (u L) `<=` smooth_compact_carrier K)->
  (a< +oo)%E->(b< +oo)%E->
  (exists k,forall L,(k<=L)%N->(M d.+1 (u L)<=a)%E)->
  (exists k,forall L,(k<=L)%N->(M d (bd d (u L))<=b)%E)->
  (@current_normal_mass R h2 n U hU d.+1 T<=a+b)%E.
Proof.
move=>hWeak hSupport hAFinite hBFinite hBound hBoundaryBound.
have[_ [hMass hBoundaryMass]]:=@normal_current_weak_closed_positive_mass_bounds
  d u T a b hWeak hSupport hAFinite hBFinite hBound hBoundaryBound.
change (M d.+1 T+M d (bd d T)<=a+b)%E.
exact:leeD hMass hBoundaryMass.
Qed.

(** Source for [normal_current_weak_closed_normal_bound]:
    the approximating currents in Federer 4.1.14, p. 370,
    are N bounded, so their flat limit is normal. This
    supporting implication needs only weak convergence,
    the original support bound and the printed degree-zero
    convention for N. It adds no representation premise.
    This compatibility adapter concludes normality only; two
    separate bounds by b do not establish N(T)<=b. *)
Theorem normal_current_weak_closed_normal_bound m
    (u : nat -> C m) (T : C m) (b : R) :
  @is_current_weak_sequence_limit R h2 n m U hU u T ->
  (forall k,
    @current_support R h2 n U hU m (u k) `<=`
      smooth_compact_carrier K) ->
  (forall k,
    (@current_normal_mass R h2 n U hU m (u k) <= b%:E)%E) ->
  @normal_currents_supported_in R h2 n U hU m K T.
Proof.
move=> hWeak hSupport hBound.
have hTSupport :=
  @current_weak_limit_support_compact R h2 n m U hU K u T
    hWeak hSupport.
split; last exact: hTSupport.
split; last exact:
  (@current_support_compact_bound R h2 n m U hU K T hTSupport).
case: m u T hWeak hSupport hBound hTSupport => [|d]
    u T hWeak hSupport hBound hTSupport.
- split; last by [].
  apply: (@current_finite_mass_representation R h2 n 0 U hU T).
  have hMass : (M 0 T <= b%:E)%E.
    apply: (@current_mass_weak_closed_bound R h2 n 0 U hU
      u T b%:E 0%N hWeak) => k _.
    exact: hBound k.
  exact: le_lt_trans hMass (ltry b).
- have hMassBound k : (M d.+1 (u k) <= b%:E)%E.
    apply: (le_trans _ (hBound k)).
    change (M d.+1 (u k) <=
      M d.+1 (u k) +
        M d (@current_boundary R h2 n d U hU (u k)))%E.
    rewrite -[leLHS](adde0 (M d.+1 (u k))).
    exact: leeD2l (@current_mass_nonnegative R h2 n d U hU
      (@current_boundary R h2 n d U hU (u k))).
  have hBoundaryBound k :
      (M d (@current_boundary R h2 n d U hU (u k)) <= b%:E)%E.
    apply: (le_trans _ (hBound k)).
    change (M d (@current_boundary R h2 n d U hU (u k)) <=
      M d.+1 (u k) +
        M d (@current_boundary R h2 n d U hU (u k)))%E.
    rewrite addeC -[leLHS](adde0
      (M d (@current_boundary R h2 n d U hU (u k)))).
    exact: leeD2l (@current_mass_nonnegative R h2 n d.+1 U hU
      (u k)).
  have hMass : (M d.+1 T <= b%:E)%E.
    apply: (@current_mass_weak_closed_bound R h2 n d.+1 U hU
      u T b%:E 0%N hWeak) => k _.
    exact: hMassBound k.
  have hBoundaryMass :
      (M d (@current_boundary R h2 n d U hU T) <= b%:E)%E.
    apply: (@current_mass_weak_closed_bound R h2 n d U hU
      (fun k => @current_boundary R h2 n d U hU (u k))
      (@current_boundary R h2 n d U hU T) b%:E 0%N
      (@current_weak_limit_boundary R h2 n d U hU u T hWeak))
      => k _.
    exact: hBoundaryBound k.
  split.
  + exact: (@current_finite_mass_representation R h2 n d.+1 U hU T
      (le_lt_trans hMass (ltry b))).
  + exact: (@current_finite_mass_representation R h2 n d U hU
      (@current_boundary R h2 n d U hU T)
      (le_lt_trans hBoundaryMass (ltry b))).
Qed.
End NormalCurrentWeakClosedBound.
