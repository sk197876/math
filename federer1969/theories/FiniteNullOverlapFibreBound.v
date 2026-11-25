(** Federer (1969), 3.2.31, p. 269: supporting summation
    over compact local pieces. Fibre masses are subadditive;
    null overlaps make source masses exactly additive. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals
  constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureBasic MeasureIntegralUP MeasureIntegralBounds
  FiniteCoverMeasureBounds FiniteNullOverlapAdditivity NonnegativeSum
  FiniteNonnegativeIntegralComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_null_overlap_fibre_integral_bound]: supporting
    the sum of locally rescaled estimates in Federer 3.2.31,
    p. 269. Pairwise source-null overlaps are sufficient;
    no disjointness or nullity in the fibre degree is assumed.
    The finite index type may be empty. Each component has
    its actual integral, and the full integrand uses actual fibres. *)
Theorem finite_null_overlap_fibre_integral_bound (R:realType) (X Y:choiceType) (I:finType)
    (alpha nu:set X->\bar R) (beta:set Y->\bar R)
    (ha:is_measure alpha) (hn:is_measure nu) (hb:is_measure beta)
    (F:X->Y) (K:set X) (C:I->set X) (q:R):
  (\bigcup_(i in @setT I) C i)=K ->
  (forall i,measure_measurable alpha (C i)) ->
  (forall i j,i!=j ->alpha (C i `&` C j)=0) ->
  (forall i,is_measure_integral beta
    (partial_function_total (fun y=>(nu (C i `&` F @^-1` [set y]):extended_real_line R)))
    (measure_upper_integral beta (partial_function_total
      (fun y=>(nu (C i `&` F @^-1` [set y]):extended_real_line R))))) ->
  (forall i,measure_upper_integral beta (partial_function_total
      (fun y=>(nu (C i `&` F @^-1` [set y]):extended_real_line R)))<=q%:E*alpha (C i)) ->
  measure_upper_integral beta (partial_function_total
    (fun y=>(nu (K `&` F @^-1` [set y]):extended_real_line R)))<=q%:E*alpha K.
Proof.
move=>hUnion hMeas hOverlap hIntegral hLocal.
pose u i y:extended_real_line R:=nu (C i `&` F @^-1` [set y]).
pose a i:=measure_upper_integral beta (partial_function_total (u i)).
have hPt y:nu (K `&` F @^-1` [set y])<=\sum_i u i y.
  apply:(@measure_finite_indexed_cover R X I nu hn _ (fun i=>C i `&` F @^-1` [set y])).
  move=>x [hx hFx]; have [i _ hxi]:(\bigcup_i C i) x by rewrite hUnion.
  exists i=>//; by split.
have hComparison:=@finite_nonnegative_integral_comparison R Y I beta hb
  (fun y=>(nu (K `&` F @^-1` [set y]):extended_real_line R)) u a
  (fun i y=>@measure_nonnegative R X nu hn _) hIntegral hPt.
have hMass:alpha K=\sum_i alpha (C i).
  have hAdd:=@measure_finite_family_null_overlap_additivity R X I alpha ha C setT
    (@finite_finset I setT) (fun i _=>hMeas i) (fun i j _ _=>hOverlap i j).
  rewrite hUnion in hAdd.
  rewrite (@finite_type_nonnegative_sum R I (fun i=>alpha (C i))
    (fun i=>@measure_nonnegative R X alpha ha (C i))) in hAdd.
  exact hAdd.
have hCosts:(\sum_i a i)<=\sum_i q%:E*alpha (C i).
  by apply:lee_sum=>i _; exact:hLocal.
have hFactor:q%:E*(\sum_i alpha (C i))=\sum_i q%:E*alpha (C i).
  apply:ge0_sume_distrr=>i _; exact (@measure_nonnegative R X alpha ha (C i)).
apply:le_trans hComparison _.
by rewrite hMass hFactor.
Qed.
