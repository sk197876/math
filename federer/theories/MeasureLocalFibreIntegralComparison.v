(** Federer (1969), 3.2.46, p. 282: local
    coarea distortion estimates assemble by countable Borel
    partitions before the distortion tends to one. The
    supporting argument retains actual source restrictions,
    whole fibres, infinite values and overlapping images. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets cardinality constructive_ereal topology.
From Federer Require Import CountableOpenBaseUP CountableBaseLindelof TopologicalBorel
  BorelPartition BorelSubordinatePartition MappingMultiplicity BorelPartitionFibreIntegral
  MeasureUP MeasureBasic MeasureRestriction MeasureFiniteClosure AreaInjectiveBorel
  PartialFunctionUP PartialFunctionBasic MeasureIntegralUP MeasureIntegralUniqueness
  NonnegativeSum NonnegativeSumScale ExtendedPowerGeometricSqueeze ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_local_fibre_integral_comparison]:
    sum proved local coarea inequalities over original
    source pieces, supporting 3.2.46, p. 282,
    by the Borel partition argument of 3.2.11,
    p. 249. No outer measure is defined by
    the desired coarea equality, and the actual global
    fibre integral is a supplied genuine integral graph. *)
Theorem measure_local_fibre_integral_comparison (R : realType) (X : topologicalType)
    (Y : choiceType) (mu nu sigma : set X -> \bar R) (beta : set Y -> \bar R)
    (f : X -> Y) (U : nat -> set X) (c : R) :
  is_measure mu -> is_measure nu -> is_measure sigma -> is_measure beta ->
  is_countable_open_base U -> (0<=c)%R ->
  (forall B, borel_set B -> measure_measurable mu B /\ measure_measurable nu B /\
    measure_measurable sigma B) ->
  (forall x, exists V : set X, open V /\ V x /\ forall S,
    measure_measurable mu S -> S `<=` V -> exists b, 0<=b /\
      is_measure_integral beta (partial_function_total
        (fun y=>(sigma (mapping_fibre f S y) : extended_real_line R))) b /\
      nu S<=c%:E*b /\ b<=c%:E*nu S) ->
  forall S a, measure_measurable mu S ->
    is_measure_integral beta (partial_function_total
      (fun y=>(sigma (mapping_fibre f S y) : extended_real_line R))) a ->
    0<=a /\ nu S<=c%:E*a /\ a<=c%:E*nu S.
Proof.
move=> hMu hNu hSigma hBeta hBase hc hBorel hLocal S a hS hIntegral.
pose C := [set V : set X | open V /\ forall T,
  measure_measurable mu T -> T `<=` V -> exists b, 0<=b /\
    is_measure_integral beta (partial_function_total
      (fun y=>(sigma (mapping_fibre f T y) : extended_real_line R))) b /\
    nu T<=c%:E*b /\ b<=c%:E*nu T].
have hOpen V : C V -> open V by move=> [hV _].
have hCover : setT `<=` \bigcup_(V in C) V.
  move=> x _; have [V [hV [hx hEstimate]]] := hLocal x.
  exists V; last exact hx; by split.
have [G [hGC [hCount hGCover]]] := countable_base_open_subcover hBase hOpen hCover.
have hGBorel V (hVG : G V) : borel_set V := open_borel_set (hOpen V (hGC V hVG)).
have [H [hH hSub]] := borel_countable_cover_subordinate_partition
  (open_borel_set (@openT X)) hCount hGBorel hGCover.
pose E B := S `&` B.
have hEMeas B (hHB : H B) : measure_measurable mu (E B).
  exact:(measure_measurable_intersection hMu hS
    (hBorel B (borel_partition_members hH hHB)).1).
have hex B : exists b, H B -> 0<=b /\
    is_measure_integral beta (partial_function_total
      (fun y=>(sigma (mapping_fibre f (E B) y) : extended_real_line R))) b /\
    nu (E B)<=c%:E*b /\ b<=c%:E*nu (E B).
  case:(pselect (H B))=> hHB; last by exists 0=> hFalse; exfalso; exact:hHB hFalse.
  have [_ [V [hVG hBV]]] := hSub B hHB.
  have [b hb] := (hGC V hVG).2 (E B) (hEMeas B hHB)
    (fun x hx=>hBV x hx.2).
  by exists b.
have [b hb] := choice hex.
have hAssembled := @borel_partition_fibre_integral R X Y sigma beta f S H b hSigma hBeta hH
  (fun B hHB=>(hBorel B (borel_partition_members hH hHB)).2.2)
  (fun B hHB=>(hb B hHB).2.1).
have hValue : a=nonnegative_sum H b := measure_integral_unique hIntegral hAssembled.
have hSum : nu S=nonnegative_sum H (fun B=>nu (E B)).
  have hRestricted := @measure_borel_partition_sum R X (measure_restrict nu S)
    (measure_restrict_is_measure hNu S) setT H hH
    (fun B hHB=>@measure_restrict_measurable R X nu S B
      (hBorel B (borel_partition_members hH hHB)).2.1).
  by rewrite /measure_restrict setIT in hRestricted.
have hb0 B (hHB : H B) : 0<=b B := (hb B hHB).1.
rewrite hValue hSum; split; first exact:nonnegative_sum_nonnegative.
split.
- rewrite -(@nonnegative_sum_scale R [the choiceType of set X] H b c hc hb0).
  apply:nonnegative_sum_mono=> B hHB; exact:(hb B hHB).2.2.1.
- rewrite -(@nonnegative_sum_scale R [the choiceType of set X] H (fun B=>nu (E B)) c hc
    (fun B _=>measure_nonnegative hNu _)).
  apply:nonnegative_sum_mono=> B hHB; exact:(hb B hHB).2.2.2.
Qed.

(** Source for [measure_local_fibre_geometric_identity]:
    let lambda tend to one after the actual Borel
    partition assembly, as in 3.2.46, p. 282.
    Both original integral values may be infinite or
    zero; the independent measure and genuine integral
    graphs precede this supporting equality theorem. *)
Theorem measure_local_fibre_geometric_identity (R : realType) (X : topologicalType)
    (Y : choiceType) (mu nu sigma : set X -> \bar R) (beta : set Y -> \bar R)
    (f : X -> Y) (U : nat -> set X) k :
  is_measure mu -> is_measure nu -> is_measure sigma -> is_measure beta ->
  is_countable_open_base U ->
  (forall B, borel_set B -> measure_measurable mu B /\ measure_measurable nu B /\
    measure_measurable sigma B) ->
  (forall lambda : R, (1<lambda)%R -> forall x,
    exists V : set X, open V /\ V x /\ forall S,
    measure_measurable mu S -> S `<=` V -> exists b, 0<=b /\
      is_measure_integral beta (partial_function_total
        (fun y=>(sigma (mapping_fibre f S y) : extended_real_line R))) b /\
      nu S<=(lambda^+k)%R%:E*b /\ b<=(lambda^+k)%R%:E*nu S) ->
  forall S a, measure_measurable mu S ->
    is_measure_integral beta (partial_function_total
      (fun y=>(sigma (mapping_fibre f S y) : extended_real_line R))) a -> a=nu S.
Proof.
move=> hMu hNu hSigma hBeta hBase hBorel hLocal S a hS hIntegral.
have hGlobal lambda (hLambda : (1<lambda)%R) :=
  @measure_local_fibre_integral_comparison R X Y mu nu sigma beta f U (lambda^+k)%R
    hMu hNu hSigma hBeta hBase (exprn_ge0 k (ltW (lt_trans ltr01 hLambda)))
    hBorel (hLocal lambda hLambda) S a hS hIntegral.
have ha : 0<=a := (hGlobal 2%R (ltr1n _ 2)).1.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply:(@extended_power_geometric_squeeze R (nu S) a k (measure_nonnegative hNu S))=> lambda hLambda.
  exact:(hGlobal lambda hLambda).2.2.
- apply:(@extended_power_geometric_squeeze R a (nu S) k ha)=> lambda hLambda.
  exact:(hGlobal lambda hLambda).2.1.
Qed.
