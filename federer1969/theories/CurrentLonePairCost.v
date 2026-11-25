(** Federer (1969), 4.1.18, p. 375: the exact
    pair cost J(xi,eta)=integral_U(mass(xi)+mass(eta)).
    Each field retains its opaque compactly supported
    L1 carrier. Raw fields carry a seminorm, with no
    positive-definiteness assertion before almost equality. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading CurrentDomain CurrentCoefficientNorms MeasureUP
  MeasureIntegralUP SummableRealFunctionUP SummableRealArithmetic
  EuclideanOpenDomainMeasure CompactSummableFieldIntegral
  CompactSummableMultivectors.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PairCost.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation A:=(@compact_summable_multivector_space R h2 n m U hU).
Local Notation B:=(@compact_summable_multivector_space R h2 n m.+1 U hU).
Local Notation P:=[the lmodType R of (A*B)%type].
Local Notation sizeA:=(@compact_summable_multivector_size R h2 n m U hU).
Local Notation sizeB:=(@compact_summable_multivector_size R h2 n m.+1 U hU).
Local Notation valueA:=(@compact_summable_multivector_value R h2 n m U hU).
Local Notation valueB:=(@compact_summable_multivector_value R h2 n m.+1 U hU).

(** Source for [current_lone_pair_cost]: the original J
    of Federer 4.1.18, p. 375, on Omega_m times
    Omega_(m+1). Its literal integral formula follows below. *)
Definition current_lone_pair_cost (v:P):R:=sizeA v.1+sizeB v.2.

(** Source for [current_lone_pair_cost_seminorm]: the
    seminorm laws required for J and its closure in
    Federer 4.1.18, pp. 375–377. *)
Theorem current_lone_pair_cost_seminorm:
  is_real_seminorm current_lone_pair_cost.
Proof.
have hA:=@compact_summable_multivector_size_laws R h2 n m U hU.
have hB:=@compact_summable_multivector_size_laws R h2 n m.+1 U hU.
constructor.
- move=>v;exact:addr_ge0 (real_seminorm_nonnegative hA v.1)
    (real_seminorm_nonnegative hB v.2).
- move=>c v;rewrite /current_lone_pair_cost /=
    (real_seminorm_scale hA) (real_seminorm_scale hB) mulrDr.
  by [].
- move=>v w;rewrite /current_lone_pair_cost /=.
  have h:=lerD (real_seminorm_triangle hA v.1 w.1)
    (real_seminorm_triangle hB v.2 w.2).
  by rewrite addrACA in h.
Qed.

(** Source for [current_lone_pair_cost_integral]: the literal
    original-U J formula of Federer 4.1.18, p. 375.
    The two coefficient masses have their original degrees. *)
Theorem current_lone_pair_cost_integral (v:P):
  is_measure_integral (@euclidean_open_domain_measure R n U)
    (real_total_integrand (fun x=>
      @current_vector_mass R h2 n m (valueA v.1 x)+
      @current_vector_mass R h2 n m.+1 (valueB v.2 x)))
    (current_lone_pair_cost v)%:E.
Proof.
apply:(@real_total_integral_add R (current_domain R n U)
  (@euclidean_open_domain_measure R n U)
  (proj1 (@euclidean_open_domain_measure_laws R n U hU))).
- exact:(@compact_summable_field_size_integral R (current_domain R n U)
    (exterior_power X m) (@current_vector_mass R h2 n m)
    (@current_vector_mass_real_norm R h2 n m)
    (@euclidean_open_domain_measure R n U)
    (proj1 (@euclidean_open_domain_measure_laws R n U hU)) v.1).
- exact:(@compact_summable_field_size_integral R (current_domain R n U)
    (exterior_power X m.+1) (@current_vector_mass R h2 n m.+1)
    (@current_vector_mass_real_norm R h2 n m.+1)
    (@euclidean_open_domain_measure R n U)
    (proj1 (@euclidean_open_domain_measure_laws R n U hU)) v.2).
Qed.
End PairCost.
