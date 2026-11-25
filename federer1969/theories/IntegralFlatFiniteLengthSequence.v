(** Federer (1969), 4.1.24, p. 382: the
    full original finite-length sequence argument. Choose
    decompositions of every increment with summable actual
    mass costs, sum both same-K rectifiable series,
    and retain T=T_1+sum Ri+boundary(sum Si) and
    every exact chosen-cost tail. Zero-based indices
    shift the printed first index by one. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces CurrentBoundary CurrentMassSealed CurrentMassBasic
  CurrentMassConvergenceUP NonnegativeSum NonnegativeSequenceTail
  RectifiableCurrentApproximationUP IntegralCurrentClassesUP IntegralCurrentAlgebra
  IntegralFlatSizeSealed IntegralFlatSeriesDecompositionUP IntegralFlatSeriesDecompositionExistence
  IntegralFlatActualSeries IntegralFlatSequenceLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section IntegralFlatFiniteLengthSequence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation Next:=(@current_space R h2 n U hU m.+1).
Local Notation M:=(fun d=>@CurrentMass.value R h2 n d U hU).
Local Notation bd:=(@current_boundary R h2 n m U hU).
Local Notation Rect:=(fun d=>@is_rectifiable_current_supported_in R h2 n d U hU K).
Local Notation IF:=(@is_integral_flat_current_supported_in R h2 n U hU m K).
Local Notation Size:=(@IntegralFlatSize.value R h2 n m U hU K).
Variable u:nat->C.
Hypothesis hUFlat:forall i,IF (u i).
Local Notation increment:=(fun i=>u i.+1-u i).
Let hIncrement i:IF (increment i):=
  @integral_flat_current_subtract_supported R h2 n U hU K m (u i.+1) (u i)
    (hUFlat i.+1) (hUFlat i).

(** Source for [integral_flat_finite_length_sequence_limit]: every
    original sequence with summable successive integral-flat
    distances has the printed current limit and the
    literal tail bound from all its chosen mass
    costs, 4.1.24, p. 382. Neither normality
    nor finite input mass is added. *)
Theorem integral_flat_finite_length_sequence_limit:
  (nonnegative_sum setT (fun i=>(Size (increment i) (hIncrement i))%:E)< +oo)%E->
  exists A:nat->C,exists B:nat->Next,exists P:C,exists Q:Next,exists T:C,
    @is_integral_flat_series_decomposition R h2 n m U hU K increment A B /\
    Rect m P /\Rect m.+1 Q /\
    @is_current_mass_sequence_limit R h2 n m U hU (fun k=>\sum_(i<k) A i) P /\
    @is_current_mass_sequence_limit R h2 n m.+1 U hU (fun k=>\sum_(i<k) B i) Q /\
    IF T /\T=u 0%N+P+bd Q /\
    (forall k,exists hResidual:IF (T-u k),
      ((Size (T-u k) hResidual)%:E<=
        nonnegative_sequence_tail (fun i=>M m (A i)+M m.+1 (B i)) k)%E) /\
    @is_integral_flat_sequence_limit R h2 n m U hU K u T.
Proof.
move=>hFinite.
have[A [B hData]]:=@integral_flat_series_decomposition_exists R h2 n m U hU K
  increment hIncrement hFinite.
have[P [Q [hP [hQ [hPLimit [hQLimit [hWeak hTail]]]]]]]:=
  @integral_flat_actual_series_exists R h2 n m U hU K increment A B hData.
pose S:=P+bd Q.
pose T:=u 0%N+S.
have hSFlat:IF S.
  exists P,Q;split;first exact:hP.
  split;[exact:hQ|by []].
have hTFlat:IF T:=@integral_flat_current_add_supported R h2 n U hU K m
  (u 0%N) S (hUFlat 0%N) hSFlat.
have hPrefix k:(\sum_(i<k) increment i)=u k-u 0%N.
  elim:k=>[|k hPrefix];first by rewrite big_ord0 subrr.
  rewrite big_ord_recr hPrefix /=.
  by rewrite (addrC (u k-u 0%N) (u k.+1-u k)) addrA subrK.
have hResidualEqual k:T-u k=S-\sum_(i<k) increment i.
  rewrite hPrefix /T;clearbody S;rewrite opprB !addrA;congr (_-u k);exact:addrC.
have hActualTail k:exists hResidual:IF (T-u k),
    ((Size (T-u k) hResidual)%:E<=
      nonnegative_sequence_tail (fun i=>M m (A i)+M m.+1 (B i)) k)%E.
  rewrite hResidualEqual;exact:hTail k.
have hLimit:@is_integral_flat_sequence_limit R h2 n m U hU K u T.
  move=>epsilon hEpsilon.
  have hPositive i:(0<=M m (A i)+M m.+1 (B i))%E.
    exact:adde_ge0 (@current_mass_nonnegative R h2 n m U hU (A i))
      (@current_mass_nonnegative R h2 n m.+1 U hU (B i)).
  have[N hN]:=@nonnegative_sequence_tail_small R
    (fun i=>M m (A i)+M m.+1 (B i)) hPositive
    (integral_flat_series_cost_summable hData) epsilon hEpsilon.
  exists N=>i hNi;have[hResidual hBound]:=hActualTail i.
  exists hResidual;have h:=le_lt_trans hBound (hN i hNi);by rewrite lte_fin in h.
exists A,B,P,Q,T;split;first exact:hData.
split;first exact:hP.
split;first exact:hQ.
split;first exact:hPLimit.
split;first exact:hQLimit.
split;first exact:hTFlat.
split;first by rewrite /T /S addrA.
split;[exact:hActualTail|exact:hLimit].
Qed.
End IntegralFlatFiniteLengthSequence.
