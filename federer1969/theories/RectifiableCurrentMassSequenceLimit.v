(** Federer (1969), 4.1.24, p. 382: a mass
    Cauchy sequence in R_(m,K) has an actual mass
    limit in that same original class. Reuse the
    complete flat space of 4.1.12, the already proved
    F_K<=M estimate, and weak lower semicontinuity of
    the original mass. The proper-filter completeness
    bridge remains separate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces CurrentSupportGeometry CurrentMassSealed
  CurrentMassConvergenceUP CurrentMassWeakConvergence CurrentMassWeakLowerLimit
  CurrentWeakSequenceLimit CurrentWeakLimitOperations
  CurrentFlatNorm CurrentFlatMassComparison CurrentFlatSequenceLimitUP
  CurrentFlatSequenceLimits FlatCurrentCauchyLimit
  RectifiableCurrentApproximationUP RectifiableCurrentBasic RectifiableCurrentMassClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section RectifiableCurrentMassSequenceLimit.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation M:=(@CurrentMass.value R h2 n m U hU).
Local Notation Rect:=(@is_rectifiable_current_supported_in R h2 n m U hU K).

(** Source for [rectifiable_current_mass_cauchy_sequence_limit]:
    the actual sequential mass-completeness assertion used
    for both rectifiable series in 4.1.24, p. 382.
    A flat limit exists in the original K. Every
    eventual mass Cauchy bound passes to that limit
    through weak mass lower semicontinuity. Mass closure
    then gives its original rectifiable membership. *)
Theorem rectifiable_current_mass_cauchy_sequence_limit (u:nat->C):
  (forall i,Rect (u i))->
  @is_current_mass_cauchy_sequence R h2 n m U hU u->
  exists T:C,Rect T /\
    @is_current_mass_sequence_limit R h2 n m U hU u T /\
    @is_current_weak_sequence_limit R h2 n m U hU u T.
Proof.
move=>hRect hCauchy.
have hFlat i:=@rectifiable_current_flat_supported R h2 n m U hU K (u i) (hRect i).
have hFlatCauchy:@is_current_flat_cauchy_sequence R h2 n m U hU K u.
  move=>epsilon hEpsilon;have[N hN]:=hCauchy epsilon hEpsilon.
  exists N=>i j hNi hNj.
  have hSupport:@current_support R h2 n U hU m (u i-u j)
      `<=` smooth_compact_carrier K.
    have h:=@current_support_linear_subset R h2 n m U hU K (-1) (u j) (u i)
      (@rectifiable_current_support R h2 n m U hU K (u j) (hRect j))
      (@rectifiable_current_support R h2 n m U hU K (u i) (hRect i)).
    by rewrite scaleN1r addrC in h.
  exact:(le_lt_trans (@current_flat_norm_le_mass R h2 n m U hU K
    (u i-u j) hSupport) (hN i j hNi hNj)).
have[T [hTFlat hFlatLimit]]:=@flat_current_cauchy_sequence_limit
  R h2 n m U hU K u hFlat hFlatCauchy.
have hWeak:=@current_flat_sequence_limit_weak R h2 n m U hU K u T hFlatLimit.
have hMassLimit:@is_current_mass_sequence_limit R h2 n m U hU u T.
  move=>epsilon hEpsilon.
  pose delta:=epsilon/2.
  have hDelta:0<delta by rewrite /delta divr_gt0 //;lra.
  have[N hN]:=hCauchy delta hDelta.
  exists N=>i hNi.
  have hDifferenceWeak:=@current_weak_limit_subtract_right R h2 n m U hU u T (u i) hWeak.
  have hClosed:=@current_mass_weak_closed_bound R h2 n m U hU
    (fun j=>u j-u i) (T-u i) delta%:E N hDifferenceWeak
    (fun j hNj=>ltW (hN j i hNj hNi)).
  apply:(le_lt_trans hClosed);rewrite lte_fin /delta;lra.
have hTRect:Rect T.
  apply:(@rectifiable_current_mass_closed R h2 n m U hU K T)=>epsilon hEpsilon.
  have[N hN]:=hMassLimit epsilon hEpsilon.
  exists (u N);split;first exact:hRect N.
  exact:hN N (leqnn N).
exists T;split;first exact:hTRect.
by split.
Qed.
End RectifiableCurrentMassSequenceLimit.
