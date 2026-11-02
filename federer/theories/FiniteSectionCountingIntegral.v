(** Supporting Federer (1969), 2.10.46, p. 204: integrate the finite fibre
    count in Freilich (1950), Theorem 4.5, Part 4, pp. 245–247, by summing
    characteristic functions. This is precisely finite additivity of the
    integral, 2.4.4–2.4.5, p. 83 Overlaps are counted with multiplicity, not
    discarded. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology
  PartialFunctionBasic MeasureUP MeasureBasic MeasureIntegralUP MeasureIntegralGraphEquivalence
  MeasureCharacteristicIntegral MeasureFiniteRealSumIntegral CharacteristicFunctionUP
  CharacteristicFunctionSealed CountingMeasure CountingConstantSum NonnegativeSum NonnegativeSumSupport NonnegativeSumRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_characteristic_count]: supporting pointwise
    counting identity for 2.10.46, p. 204; Freilich
    (1950), Theorem 4.5, Part 4, pp. 245–247.
    Each qualifying finite index contributes one, including when
    several indices describe identical subsets. *)
Lemma finite_characteristic_count (R : realType) (X : Type) (J : choiceType)
    (F : {fset J}) (S : J -> set X) (s : J -> X -> R) :
  (forall j, is_characteristic_function (S j) (s j)) -> forall x,
  counting_measure (R:=R) [set j | j \in F /\ S j x]=(\sum_(j <- F) s j x)%R%:E.
Proof.
move=> hs x.
have he : [set j | j \in F /\ S j x]=[set` F] `&` [set j | S j x] by [].
rewrite he counting_measure_sum -nonnegative_sum_restrict.
have heq j : (if j \in [set j | S j x] then (1 : \bar R) else 0)=(s j x)%:E.
  case: (pselect (S j x))=> hx.
  - have hj : j \in [set j | S j x] := mem_set hx.
    by rewrite hj (characteristic_on_set (hs j) hx).
  - have hj : j \notin [set j | S j x] by apply/negP=> /set_mem hh; exact: hx hh.
    by rewrite (negbTE hj) (characteristic_off_set (hs j) hx).
have hsum : nonnegative_sum [set` F] (fun j=>if j \in [set j | S j x] then 1 else 0)=
    nonnegative_sum [set` F] (fun j=>(s j x)%:E).
  apply: nonnegative_sum_ext=> j hj; exact: heq.
rewrite hsum nonnegative_sum_finite; first by rewrite sumEFin.
move=> j hj; case: (pselect (S j x))=> hx.
- by rewrite (characteristic_on_set (hs j) hx) lee_fin ler01.
- by rewrite (characteristic_off_set (hs j) hx) lexx.
Qed.

(** Source for [finite_section_count_integral]: supporting finite
    fibre integral in 2.10.46, p. 204; Freilich
    (1950), Theorem 4.5, Part 4, pp. 245–247.
    Integrating the number of indexed measurable sets containing
    a point gives the sum of their measures. The sets may
    overlap and may have infinite measure; the index family is finite. *)
Theorem finite_section_count_integral (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (F : {fset J}) (S : J -> set X) :
  (forall j, j \in F -> measure_measurable mu (S j)) ->
  is_measure_integral mu (partial_function_total
    (fun x=>(counting_measure (R:=R) [set j | j \in F /\ S j x] : extended_real_line R)))
    (\sum_(j <- F) mu (S j)).
Proof.
move=> hS.
pose s j := @CharacteristicFunction.value R X (S j).
have hs j : is_characteristic_function (S j) (s j) := CharacteristicFunction.laws R (S j).
have hi := @measure_finite_real_sum_integral R X J mu hm (F : seq J)
  (fun j x=>(s j x : real_line_metric R)) (fun j=>mu (S j))
  (fun j _=>measure_nonnegative hm (S j))
  (fun j hj=>@measure_characteristic_integral R X mu hm (S j) (s j) (hs j) (hS j hj)).
apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ hi)=> x z.
change ((exists r : R, (\sum_(j <- F) s j x)%R=r /\ r%:E=z) <->
    counting_measure (R:=R) [set j | j \in F /\ S j x]=z).
rewrite (finite_characteristic_count F hs x).
split; first by move=> [r [<- hz]].
move=> hz; exists (\sum_(j <- F) s j x)%R; by split.
Qed.

(** Source for [finite_equal_section_count_integral]: supporting
    equal-length summation in 2.10.46, p. 204;
    Freilich (1950), Theorem 4.5, Part 4,
    pp. 245–247. Finite many translates of the
    same measurable scalar set have the same measure;
    their counting integral is that common measure times
    the number of fibres, even when the translates overlap. *)
Theorem finite_equal_section_count_integral (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (F : {fset J})
    (S : J -> set X) (c : R) :
  (0<=c)%R -> (forall j, j \in F -> measure_measurable mu (S j)) ->
  (forall j, j \in F -> mu (S j)=c%:E) ->
  is_measure_integral mu (partial_function_total
    (fun x=>(counting_measure (R:=R) [set j | j \in F /\ S j x] : extended_real_line R)))
    (c%:E*counting_measure (R:=R) [set` F]).
Proof.
move=> hc hS he; have hi := @finite_section_count_integral R X J mu hm F S hS.
have hv : (\sum_(j <- F) mu (S j))=c%:E*counting_measure (R:=R) [set` F].
  rewrite -nonnegative_constant_sum_counting // nonnegative_sum_finite.
  - apply: eq_big_seq=> j hj; exact: he.
  - by move=> j hj; rewrite lee_fin.
by rewrite hv in hi.
Qed.
