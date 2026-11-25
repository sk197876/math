(** Federer (1969), 4.1.18, p. 375: a
    literal scalar-action average has support in a
    closed common carrier of its nonzero-weight
    currents. Reuse the original functional support
    definition; no vector-valued current integral is
    assumed.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct CurrentSpaces CurrentSupportGeometry CurrentSupportAgreement
  FunctionalSupportUP SummableRealFunctionUP MeasureIntegralUP MeasureIntegralUniqueness
  LatticeL1ApproximationLaws MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentScalarAverageSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation C:=(@current_space R h2 n Full hFull m).
Local Notation DT:=(@current_test_space R h2 n Full hFull m).
Local Notation action:=(@current_value R h2 n Full hFull m).
Variable P:choiceType.
Variable mu:set P->\bar R.
Hypothesis hm:is_measure mu.
Variables (w:P->R) (S:P->C) (Q:C).
Hypothesis hAction:forall omega:DT,is_measure_integral mu
  (real_total_integrand (fun z=>w z*action (S z) omega)) (action Q omega)%:E.
Variable K:set X.
Hypothesis hClosed:@closed (real_norm_metric_space hNX) K.
Hypothesis hSupport:forall z,w z<>0 ->@current_support R h2 n Full hFull m (S z) `<=` K.

(** Source for [current_scalar_average_support]: the support
    comparison for both original smoothing operators,
    Federer 4.1.18, p. 375. Vanishing weights
    impose no restriction on their currents. *)
Theorem current_scalar_average_support:
  @current_support R h2 n Full hFull m Q `<=` K.
Proof.
move=>x [hx hNot];apply:contrapT=>hxOff.
apply:hNot;exists (~` K);split;last exact:hxOff.
split;first exact:closed_openC hClosed.
move=>omega hOmega.
have hZero:(fun z=>w z*action (S z) omega)=(fun _:P=>(0:R)).
  apply:funext=>z;case:(pselect (w z=0))=>[->|hz];first exact:mul0r.
  have hValue:action (S z) omega=0.
    apply:(@current_test_disjoint_support_zero R h2 n m Full hFull (S z) omega)=>y hy hTest.
    exact:((@hOmega y hTest) (@hSupport z hz y hy)).
  by rewrite hValue mulr0.
have hIntegral:=hAction omega;rewrite hZero in hIntegral.
exact:(EFin_inj (measure_integral_unique hIntegral
  (@real_total_zero_integral R P mu hm))).
Qed.
End CurrentScalarAverageSupport.
