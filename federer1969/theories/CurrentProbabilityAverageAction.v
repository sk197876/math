(** Federer (1969), 4.1.18, p. 374: subtract
    an original current from its literal probability
    average by integrating the actual current
    differences. Only finite scalar actions are
    subtracted.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentPointEvaluation MeasureUP MeasureIntegralUP
  SummableRealFunctionUP SummableRealArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_probability_average_difference_action]:
    integral w(z)(S_z−T) equals Q−T when
    integral w=1 and Q is the original scalar
    average, by 2.4.4(3)–(4), supporting
    the homotopy formulas of 4.1.18, p. 374. *)
Theorem current_probability_average_difference_action
    (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (P:choiceType) (mu:set P->\bar R) (hm:is_measure mu)
    (w:P->R) (S:P->@current_space R h2 n U hU m)
    (Q T:@current_space R h2 n U hU m)
    (hUnit:is_measure_integral mu (real_total_integrand w) 1%:E)
    (hQ:forall omega:@current_test_space R h2 n U hU m,
      is_measure_integral mu
        (real_total_integrand (fun z=>w z*@current_value R h2 n U hU m (S z) omega))
        (@current_value R h2 n U hU m Q omega)%:E)
    (omega:@current_test_space R h2 n U hU m):
  is_measure_integral mu
    (real_total_integrand (fun z=>w z*@current_value R h2 n U hU m (S z-T) omega))
    (@current_value R h2 n U hU m (Q-T) omega)%:E.
Proof.
pose action:=@current_value R h2 n U hU m.
have hSubtract (A B:@current_space R h2 n U hU m):
    action (A-B) omega=action A omega-action B omega.
  change (@current_point_evaluation R h2 n m U hU omega (A-B)=
    @current_point_evaluation R h2 n m U hU omega A-
    @current_point_evaluation R h2 n m U hU omega B).
  exact:linearB.
have hConstant:=@real_total_integral_scale R P mu hm w 1
  (action T omega) hUnit.
rewrite mulr1 in hConstant.
have hDifference:=@real_total_integral_subtract R P mu hm
  (fun z=>w z*action (S z) omega) (fun z=>action T omega*w z)
  (action Q omega) (action T omega) (hQ omega) hConstant.
have hFunction:(fun z=>w z*action (S z) omega-action T omega*w z)=
    (fun z=>w z*action (S z-T) omega).
  apply:funext=>z;rewrite hSubtract;ring.
by rewrite hFunction -hSubtract in hDifference.
Qed.
