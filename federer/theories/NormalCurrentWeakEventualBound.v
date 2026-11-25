(** Federer (1969), 4.1.14, p. 370: the smooth image
    sequence is N bounded, and its supports eventually lie
    in the prescribed compact E. Its weak limit is normal.
    Keep the eventual support condition and the degree-zero
    exception; do not infer the same N cap for the limit
    from two separate mass caps. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentBoundary SmoothCompactSet NormalCurrentsUP
  CurrentMassSealed CurrentMassBasic CurrentWeakSequenceLimit
  NormalCurrentWeakClosedBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [normal_current_weak_eventual_normal_bound]: the
    normality passage in Federer 4.1.14, p. 370. The current
    and boundary representation witnesses are consequences of
    finite mass, not assumptions on the weak limit. *)
Theorem normal_current_weak_eventual_normal_bound
    (R:realType) (h2:(1+1:R)!=0) n m (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (u:nat->@current_space R h2 n U hU m)
    (T:@current_space R h2 n U hU m) (b:R):
  @is_current_weak_sequence_limit R h2 n m U hU u T ->
  (exists k,forall i,(k<=i)%N->
    @current_support R h2 n U hU m (u i) `<=` smooth_compact_carrier K) ->
  (forall i,(@current_normal_mass R h2 n U hU m (u i)<=b%:E)%E) ->
  @normal_currents_supported_in R h2 n U hU m K T.
Proof.
case:m u T=>[|d] u T hWeak hSupport hBound.
- exact:(@normal_current_weak_closed_zero_mass_bound R h2 n U hU K
    u T b%:E hWeak hSupport (ltry b) (ex_intro _ 0%N
      (fun i _=>hBound i))).1.
- have hMass i:(@CurrentMass.value R h2 n d.+1 U hU (u i)<=b%:E)%E.
    apply:(le_trans _ (hBound i)).
    change (@CurrentMass.value R h2 n d.+1 U hU (u i)<=
      @CurrentMass.value R h2 n d.+1 U hU (u i)+
      @CurrentMass.value R h2 n d U hU
        (@current_boundary R h2 n d U hU (u i)))%E.
    exact:leeDl _ (@current_mass_nonnegative R h2 n d U hU
      (@current_boundary R h2 n d U hU (u i))).
  have hBoundary i:(@CurrentMass.value R h2 n d U hU
      (@current_boundary R h2 n d U hU (u i))<=b%:E)%E.
    apply:(le_trans _ (hBound i)).
    change (@CurrentMass.value R h2 n d U hU
        (@current_boundary R h2 n d U hU (u i))<=
      @CurrentMass.value R h2 n d.+1 U hU (u i)+
      @CurrentMass.value R h2 n d U hU
        (@current_boundary R h2 n d U hU (u i)))%E.
    exact:leeDr _ (@current_mass_nonnegative R h2 n d.+1 U hU (u i)).
  exact:(@normal_current_weak_closed_positive_mass_bounds R h2 n U hU K
    d u T b%:E b%:E hWeak hSupport (ltry b) (ltry b)
    (ex_intro _ 0%N (fun i _=>hMass i))
    (ex_intro _ 0%N (fun i _=>hBoundary i))).1.
Qed.
