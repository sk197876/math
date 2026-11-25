(** Federer (1969), 4.1.12, pp. 368–369:
    original testwise current limits preserve fixed compact
    supports, positive-degree boundaries and subtraction of
    a fixed current. Eventually constant test values have
    their stated limits. Reuse the original test actions
    and uniqueness of scalar norm limits. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology ring.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentPointEvaluation CurrentBoundary
  CurrentTestExteriorDerivative CurrentWeakSequenceLimit NormSequenceLimitUnique
  SmoothCompactSet CurrentSupportGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentWeakLimitOperations.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation C d := (@current_space R h2 n U hU d).
Local Notation action d := (@current_value R h2 n U hU d).

(** Source for [current_weak_limit_eventual_value]:
    an original test value constant on all sufficiently
    late partial sums has that same value on
    the current series, supporting Federer 4.1.12,
    pp. 368–369. *)
Theorem current_weak_limit_eventual_value (u:nat->C m) (T:C m)
    (phi:@current_test_space R h2 n U hU m) c N:
  @is_current_weak_sequence_limit R h2 n m U hU u T->
  (forall k,(N<=k)%N->action m (u k) phi=c)->action m T phi=c.
Proof.
move=>hWeak hValue.
apply:(@norm_sequence_limit_unique R R^o (fun t:R^o=>`|t|) (@scalar_absolute_value_norm R)
  (fun k=>action m (u k) phi) (action m T phi) c (hWeak phi)).
move=>epsilon hEpsilon;exists N=>k hNk.
by rewrite (hValue k hNk) subrr normr0.
Qed.

(** Source for [current_weak_limit_support_compact]:
    one original compact support bound is preserved
    by convergence on all original tests, supporting
    both series of Federer 4.1.12, pp. 368–369.
    No representation premise is added. *)
Theorem current_weak_limit_support_compact (K:smooth_compact_set hNX U)
    (u:nat->C m) (T:C m):
  @is_current_weak_sequence_limit R h2 n m U hU u T->
  (forall k,@current_support R h2 n U hU m (u k) `<=` smooth_compact_carrier K)->
  @current_support R h2 n U hU m T `<=` smooth_compact_carrier K.
Proof.
move=>hWeak hSupport.
apply:(@current_support_compact_criterion R h2 n m U hU K T).2=>phi hPhi.
apply:(@current_weak_limit_eventual_value u T phi 0 0%N hWeak)=>k _.
exact:((@current_support_compact_criterion R h2 n m U hU K (u k)).1 (hSupport k) phi hPhi).
Qed.

(** Source for [current_weak_limit_subtract_right]:
    subtracting one fixed original current preserves
    testwise limits, supporting the mass-tail arguments
    of Federer 4.1.12, pp. 368–369. *)
Theorem current_weak_limit_subtract_right (u:nat->C m) (T Q:C m):
  @is_current_weak_sequence_limit R h2 n m U hU u T->
  @is_current_weak_sequence_limit R h2 n m U hU (fun k=>u k-Q) (T-Q).
Proof.
move=>hWeak phi epsilon hEpsilon.
have[k hk]:=hWeak phi epsilon hEpsilon.
exists k=>L hKL.
pose E:=@current_point_evaluation R h2 n m U hU phi.
have hDifference:action m (u L-Q) phi-action m (T-Q) phi=action m (u L) phi-action m T phi.
  change (E (u L-Q)-E (T-Q)=E (u L)-E T).
  rewrite !(linB (hom_linear E));ring.
rewrite hDifference;exact:hk L hKL.
Qed.

(** Source for [current_weak_limit_boundary]: the
    original positive-degree boundary commutes with testwise
    limits, because boundary T(phi)=T(d phi),
    supporting Federer 4.1.12, pp. 368–369.
    No negative-degree boundary is introduced. *)
Theorem current_weak_limit_boundary (u:nat->C m.+1) (T:C m.+1):
  @is_current_weak_sequence_limit R h2 n m.+1 U hU u T->
  @is_current_weak_sequence_limit R h2 n m U hU
    (fun k=>@current_boundary R h2 n m U hU (u k)) (@current_boundary R h2 n m U hU T).
Proof.
move=>hWeak phi epsilon hEpsilon.
have[k hk]:=hWeak (@current_test_exterior_derivative R h2 n m U hU phi) epsilon hEpsilon.
exists k=>L hKL;rewrite !current_boundary_evaluation;exact:hk L hKL.
Qed.
End CurrentWeakLimitOperations.
