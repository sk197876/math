(** Federer (1969), 4.1.7, p. 358:
    compact scalar tests against the mass-density
    measure use exactly the change-of-density law
    2.4.10, p. 85. This is only a
    total finite-real graph adapter of that law. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology MeasureAlmostBasic PartialFunctionUP PartialFunctionBasic PartialZeroExtension PartialDensityProduct PartialExtendedOrderLoci
  MeasureUP MeasureAlmostUP MeasurableFunctionUP MeasureIntegralUP MeasureIntegralGraphEquivalence
  SummableRealFunctionUP MeasureDensityUP MeasureChangeOfDensity MeasureSubsetIntegral MeasureBoundGraphEquivalence
  RealSubsetIntegralGraph MeasureIntegralBounds MeasureIntegralUniqueness LatticeL1ApproximationLaws
  DensityNullWeightChange RegularMeasureUP CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureCharacteristicRegular.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_real_density_zero_locus_null]:
    the original density measure vanishes on
    the zero locus of its finite density,
    supporting Federer 4.1.7, p. 358, by
    2.4.10, p. 85. The exact zero
    extension proves this even before any
    measurability of that locus is used. *)
Lemma finite_real_density_zero_locus_null (R:realType) (X:choiceType)
    (mu nu:set X->\bar R) (hm:is_measure mu) (k:X->R):
  is_measure_density mu (real_total_integrand k) nu ->nu [set x|k x=0]=0%E.
Proof.
move=>hn.
have hZero:=@real_total_zero_integral R X mu hm.
have hOn x:k x=0 ->(0:R)=k x by move=>->.
have hOff x:~(k x=0) ->(0:R)=0 by [].
have hSubset:=(@real_subset_integral_total R X mu [set x|k x=0] k (fun _=>0) 0%E hOn hOff).2 hZero.
rewrite (hn [set x|k x=0]) /measure_subset_upper_integral.
exact:(@measure_upper_integral_unique R X mu _ _ _
  (measure_upper_integral_specification _ _) hSubset.2.1).
Qed.

(** Source for [finite_real_density_weight_agreement]:
    equality almost everywhere for the density
    measure gives equality of the original
    weighted real functions, supporting Federer
    4.1.7, p. 358, by 2.4.10, p. 85.
    The unweighted functions need not be measurable
    for the original measure. *)
Lemma finite_real_density_weight_agreement (R:realType) (X:choiceType)
    (mu nu:set X->\bar R) (hm:is_measure mu) (k f g:X->R):
  is_measure_density mu (real_total_integrand k) nu ->
  is_measure_measurable_function mu (real_total_integrand k) ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus (real_total_integrand k)) ->
  measure_almost_everywhere nu [set x|f x=g x] ->
  measure_almost_everywhere mu [set x|f x*k x=g x*k x].
Proof.
move=>hn hk hp hAgree.
have hProducts:=@density_null_real_weight_change R X mu nu hm
  (real_total_integrand k) f g hn hk hp hAgree.
have hGraph (v:X->R) x z:
    partial_function_graph (partial_density_product
      (partial_function_total (fun x=>(v x)%:E:extended_real_line R)) (real_total_integrand k)) x z <->
    partial_function_graph (real_total_integrand (fun x=>v x*k x)) x z.
  rewrite partial_density_product_graph.
  split.
  - move=>[a [b [ha [hb hProduct]]]].
    change ((v x)%:E=a) in ha.
    move/real_total_integrand_graph:hb=>hb.
    apply/real_total_integrand_graph.
    by rewrite -ha -hb -EFinM in hProduct.
  - move/real_total_integrand_graph=>hProduct.
    exists (v x)%:E,(k x)%:E; split; first by [].
    split; first by apply/real_total_integrand_graph.
    by rewrite -EFinM.
apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hProducts)=>x [z [hf hg]].
have hfz:((f x*k x)%:E=z).
  have h:=(hGraph f x z).1 hf; by move/real_total_integrand_graph:h.
have hgz:((g x*k x)%:E=z).
  have h:=(hGraph g x z).1 hg; by move/real_total_integrand_graph:h.
exact:EFin_inj (eq_trans hfz (esym hgz)).
Qed.

(** Source for [regular_measure_unit_density_value]:
    the original constant-one density gives back
    every outer measure of a regular measure,
    supporting Federer 4.1.7, p. 358, by
    2.4.5, p. 84, and 2.4.10, p. 85.
    No measurability of the target set is added. *)
Lemma regular_measure_unit_density_value (R:realType) (X:choiceType)
    (mu nu:set X->\bar R) (hm:is_measure mu):
  is_regular_measure mu ->is_measure_density mu (real_total_integrand (fun _=>1)) nu ->
  forall A,nu A=mu A.
Proof.
move=>hr hn A.
pose s:=@CharacteristicFunction.value R X A.
have hs:=@CharacteristicFunction.laws R X A.
have hGraph:=@real_subset_total_graph R X A (fun _=>1) s
  (fun x hx=>characteristic_on_set hs hx) (fun x hx=>characteristic_off_set hs hx).
rewrite (hn A) /measure_subset_upper_integral
  (@measure_upper_integral_graph_equivalent R X mu _ _ hGraph).
exact:(@regular_measure_characteristic_upper_integral R X mu hm A s hs hr).
Qed.

(** Source for [real_finite_density_total_laws]:
    the embedded finite-real density and its
    literal total extended-real graph define the
    same measure, supporting Federer 4.1.7,
    p. 358, by 2.4.10, p. 85. *)
Lemma real_finite_density_total_laws (R:realType) (X:choiceType)
    (mu nu:set X->\bar R) (k:X->R):
  is_measure_density mu (real_total_integrand k) nu ->
  is_measure_density mu (partial_function_total (fun x=>(k x)%:E:extended_real_line R)) nu.
Proof.
move=>hn A; rewrite (hn A) /measure_subset_upper_integral.
apply:measure_upper_integral_graph_equivalent=>x z.
rewrite !partial_function_zero_extension_graph real_total_integrand_graph.
by [].
Qed.

(** Source for [real_finite_density_product_graph]:
    the original density product is the ordinary
    product for finite real-valued factors, supporting
    Federer 4.1.7, p. 358, by 2.4.10,
    p. 85. No undefined extended-real product
    is replaced by a default value. *)
Lemma real_finite_density_product_graph (R:realType) (X:Type) (f h:X->R) x z:
  partial_function_graph (partial_density_product (real_total_integrand f)
    (real_total_integrand h)) x z <->
  partial_function_graph (real_total_integrand (fun x=>f x*h x)) x z.
Proof.
rewrite partial_density_product_graph.
split.
- move=>[a [b [ha [hb hProduct]]]].
  move/real_total_integrand_graph:ha=>ha.
  move/real_total_integrand_graph:hb=>hb.
  apply/real_total_integrand_graph.
  by rewrite -ha -hb -EFinM in hProduct.
- move/real_total_integrand_graph=>hProduct.
  exists (f x)%:E,(h x)%:E; split; first by apply/real_total_integrand_graph.
  split; first by apply/real_total_integrand_graph.
  by rewrite -EFinM.
Qed.

(** Source for [real_finite_density_integral_iff]:
    the exact change-of-density integral formula
    for the original finite mass density, supporting
    Federer 4.1.7, p. 358, by 2.4.10,
    p. 85. Both directions retain every integral
    value, including infinite values. *)
Lemma real_finite_density_integral_iff (R:realType) (X:choiceType)
    (mu nu:set X->\bar R) (hm:is_measure mu) (h f:X->R):
  is_measure_density mu (real_total_integrand h) nu ->
  is_measure_measurable_function mu (real_total_integrand h) ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus (real_total_integrand h)) ->
  is_measure_measurable_function mu (real_total_integrand f) ->forall a,
  is_measure_integral nu (real_total_integrand f) a <->
  is_measure_integral mu (real_total_integrand (fun x=>f x*h x)) a.
Proof.
move=>hn hh hp hf a.
have hIff:=@measure_density_integral_iff R X mu nu hm (real_total_integrand h)
  (real_total_integrand f) hn hh hp hf a.
split=>hi.
- exact:(measure_integral_graph_equivalent (real_finite_density_product_graph f h) (hIff.1 hi)).
- apply:hIff.2.
  apply:(@measure_integral_graph_equivalent R X mu _ _ a _ hi)=>x z.
  exact:iff_sym (real_finite_density_product_graph f h x z).
Qed.
