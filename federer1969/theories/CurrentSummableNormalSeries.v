(** Federer (1969), 4.1.12, pp. 368–369:
    supported normal currents with summable mass
    bounds have an actual flat series sum.
    Apply the preceding complete-flat-space theorem
    to the exact real tails of the
    original numerical sum of 2.1.1. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentMassSealed SmoothCompactSet
  NormalCurrentsUP FlatCurrentsUP CurrentWeakSequenceLimit NormalCurrentFinitePrefix
  NonnegativeSum NonnegativeSequenceTail NonnegativeRealSeriesTails.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_summable_normal_series_exists]:
    the literal finite-prefix current series exists,
    is flat in the original common K
    and has every exact numerical mass-tail
    bound. This supports both actual examples
    in Federer 4.1.12, pp. 368–369,
    without adding representation to arbitrary limits. *)
Theorem current_summable_normal_series_exists (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (v:nat->@current_space R h2 n U hU m) (a:nat->R):
  (forall k,@normal_currents_supported_in R h2 n U hU m K (v k))->
  (forall k,0<=a k)->(nonnegative_sum setT (fun k=>(a k)%:E)< +oo)%E->
  (forall k,(@CurrentMass.value R h2 n m U hU (v k)<=(a k)%:E)%E)->
  exists S:@current_space R h2 n U hU m,
    @is_flat_current_supported_in R h2 n m U hU K S /\
    @is_current_weak_sequence_limit R h2 n m U hU (fun k=>\sum_(j<k) v j) S /\
    forall k,(@CurrentMass.value R h2 n m U hU (S-\sum_(j<k) v j)<=
      nonnegative_sequence_tail (fun j=>(a j)%:E) k)%E.
Proof.
move=>hV ha hFinite hMass.
pose t:=nonnegative_real_series_tail a.
have hT k:0<=t k:=@nonnegative_real_series_tail_nonnegative R a hFinite k.
have hStep k:(@CurrentMass.value R h2 n m U hU (v k)<=(t k-t k.+1)%:E)%E.
  rewrite (@nonnegative_real_series_tail_step R a ha hFinite k);exact:hMass k.
have hSmall epsilon:0<epsilon->exists k,t k<epsilon.
  move=>hEpsilon.
  have[k hk]:=@nonnegative_real_series_tail_small R a ha hFinite epsilon hEpsilon.
  exists k;exact:hk k (leqnn k).
have[S [hFlat [hTail hWeak]]]:=@normal_current_mass_series_exists R h2 n m U hU K v t hV hT hStep hSmall.
exists S;split;first exact:hFlat.
split;first exact:hWeak.
move=>k;rewrite (@nonnegative_real_series_tail_value R a hFinite k);exact:hTail k.
Qed.
