(** Federer (1969), 4.1.18, p. 375: the
    original flat norm of q(xi,eta) is at most
    its exact L1 pair cost J when the fields
    share a compact carrier. The preceding mass
    decomposition inequality of 4.1.12, pp. 367–368,
    proves this estimate independently of the separate
    normal-approximation argument for flat membership. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology functions.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  CurrentDomain CurrentSpaces CurrentBoundary CurrentBoundarySupport
  CurrentSupportGeometry CurrentFlatNorm CurrentFlatMassComparison
  SmoothCompactSet CompactSummableMultivectors CompactSummableMultivectorDensity
  CompactSummableMultivectorSupport CurrentLonePairImageUP
  CurrentLonePairImageSealed CurrentLonePairCost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FlatBound.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation UT:=(current_domain R n U).
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation Next:=(@current_space R h2 n U hU m.+1).
Local Notation P:=(@current_lone_pair_space R h2 n m U hU).
Local Notation q:=(@CurrentLonePair.map R h2 n m U hU).
Local Notation J:=(@current_lone_pair_cost R h2 n m U hU).
Local Notation A:=(@compact_summable_multivector_current R h2 n m U hU).
Local Notation B:=(@compact_summable_multivector_current R h2 n m.+1 U hU).
Local Notation bd:=(@current_boundary R h2 n m U hU).
Local Notation valueA:=(@compact_summable_multivector_value R h2 n m U hU).
Local Notation valueB:=(@compact_summable_multivector_value R h2 n m.+1 U hU).
Local Notation support:=(@current_support R h2 n U hU m).
Local Notation supportNext:=(@current_support R h2 n U hU m.+1).

(** Source for [current_lone_pair_flat_bound]:
    F_K(q(xi,eta))<=J(xi,eta), the sharp estimate
    in the first proposition of Federer 4.1.18,
    p. 375. It holds on every common compact
    carrier, without a smoothness or flatness premise. *)
Theorem current_lone_pair_flat_bound (v:P) (K:smooth_compact_set hNX U):
  (forall x:UT,~smooth_compact_carrier K (set_val x)->valueA v.1 x=0)->
  (forall x:UT,~smooth_compact_carrier K (set_val x)->valueB v.2 x=0)->
  (@current_flat_norm R h2 n m U hU K (q v)<=(J v)%:E)%E.
Proof.
move=>hOffA hOffB.
have hA:support (A v.1) `<=` smooth_compact_carrier K.
  exact:(@compact_summable_multivector_current_support R h2 n m U hU v.1 K hOffA).
have hB:supportNext (B v.2) `<=` smooth_compact_carrier K.
  exact:(@compact_summable_multivector_current_support R h2 n m.+1 U hU v.2 K hOffB).
have hBoundary:support (bd (B v.2)) `<=` smooth_compact_carrier K.
  move=>x hx;exact:(hB x (@current_boundary_support_subset R h2 n m U hU (B v.2) x hx)).
have hSum:=@current_support_linear_subset R h2 n m U hU K 1 (A v.1)
  (bd (B v.2)) hA hBoundary.
rewrite scale1r in hSum.
have hQ:support (q v) `<=` smooth_compact_carrier K.
  by rewrite CurrentLonePair.laws.
have hBound:=@current_flat_decomposition_lower_bound R h2 n m U hU K
  (q v) (B v.2) hQ hB.
have hResidual:q v-bd (B v.2)=A v.1.
  by rewrite CurrentLonePair.laws addrK.
rewrite hResidual
  (@compact_summable_multivector_current_mass R h2 n m U hU v.1)
  (@compact_summable_multivector_current_mass R h2 n m.+1 U hU v.2)
  -EFinD in hBound.
exact:hBound.
Qed.
End FlatBound.
