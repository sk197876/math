(** Supporting countable triangle bound for Federer (1969), 2.10.9, p. 175,
    from the seminorm and lower-limit laws of 2.4.12, pp. 86–87. Finite
    partial sums of nonnegative scalar Lp functions have a common norm bound
    if the sum of their norms is finite. The already proved bounded
    increasing Lp replacement then supplies their sum almost everywhere. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureAlmostUP MeasureAlmostBasic TotalScalarLpUP
  TotalScalarLpIncreasingLimit ScalarLpFiniteSums NonnegativeSum NonnegativeSumSupport
  CountableFiniteExhaustionUP CountableFiniteExhaustionSealed FiniteExhaustionSumLimit
  ExtendedIncreasingLimitSupremum ExtendedRealOrderLimit RealLowerLimitReplacement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [scalar_lp_countable_positive_bound]: supporting
    countable triangle inequality for the cost-cover hypothesis
    in Federer 2.10.9, p. 175. The scalar representative is
    an existence conclusion; the pointwise extended sum need
    not be finite everywhere. Includes the empty index family. *)
Theorem scalar_lp_countable_positive_bound (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (t : \bar R)
    (D : set J) (u : J -> X -> R) :
  countable D -> 1<=t -> (forall j, D j -> total_scalar_lp mu t (u j)) ->
  (forall j x, (0<=u j x)%R) ->
  nonnegative_sum D (fun j => total_scalar_lp_norm mu t (u j))< +oo ->
  exists g : X -> R, total_scalar_lp mu t g /\ (forall x, (0<=g x)%R) /\
    total_scalar_lp_norm mu t g<=nonnegative_sum D (fun j => total_scalar_lp_norm mu t (u j)) /\
    measure_almost_everywhere mu [set x |
      nonnegative_sum D (fun j => (u j x)%:E)=(g x)%:E].
Proof.
move=> hD ht hu hu0 hfin.
pose a := nonnegative_sum D (fun j => total_scalar_lp_norm mu t (u j)).
have ha0 : 0<=a := nonnegative_sum_nonnegative _ _.
have hnum : a \is a fin_num by rewrite (ge0_fin_numE ha0).
pose M := fine a.
have ha : a=M%:E by rewrite /M fineK.
pose C := @CountableFiniteExhaustion.value J D hD.
have hC := @CountableFiniteExhaustion.laws J D hD.
pose v k x := (\sum_(j <- C k) u j x)%R.
have hmem k : total_scalar_lp mu t (v k).
  exact: (@scalar_lp_finite_sum_bound R X J mu hm t (C k) u ht
    (fun j hj => hu j (@finite_exhaustion_subset J D C hC k j hj))).1.
have he k x : (v k x)%:E=nonnegative_sum [set j | j \in C k] (fun j => (u j x)%:E).
  rewrite nonnegative_sum_finite; last by move=> j _; rewrite lee_fin; exact: hu0.
  by rewrite /v sumEFin.
have hv0 k x : (0<=v k x)%R.
  have hn := @nonnegative_sum_nonnegative R J [set j | j \in C k] (fun j => (u j x)%:E).
  by rewrite -(he k x) lee_fin in hn.
have hvinc k l x : (k<=l)%N -> (v k x<=v l x)%R.
  move=> hkl; rewrite -lee_fin !he; apply: nonnegative_sum_subset.
  move=> j hj; exact: (fsubsetP (@finite_exhaustion_increasing J D C hC k l hkl)) j hj.
have hvbound k : total_scalar_lp_norm mu t (v k)<=M%:E.
  rewrite -ha; apply: le_trans (@scalar_lp_finite_sum_bound R X J mu hm t (C k) u ht
    (fun j hj => hu j (@finite_exhaustion_subset J D C hC k j hj))).2 _.
  exact: (@nonnegative_sum_upper R J D (fun j => total_scalar_lp_norm mu t (u j)) (C k)
    (fun j hj => @finite_exhaustion_subset J D C hC k j hj)).
have [hg [hg0 [hgb hglim]]] := @bounded_increasing_lp_replacement R X mu hm t M v hmem hv0 hvinc hvbound.
exists (real_lower_limit_replacement v); split=> //; split=> //; split; first by rewrite -/a ha.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hglim)=> x hx.
have hs := @finite_exhaustion_nonnegative_sum_limit R J D C (fun j => (u j x)%:E) hC
  (fun j hj => (hu0 j x : 0<=(u j x)%:E)).
have hseq : (fun k => \sum_(j <- C k) (u j x)%:E)=(fun k => (v k x)%:E).
  by apply: funext=> k; rewrite /v sumEFin.
rewrite hseq in hs; exact: (extended_order_limit_unique hs.2 hx.2).
Qed.
