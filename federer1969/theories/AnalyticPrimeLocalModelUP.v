(** Federer (1969), 3.4.8(10), pp. 327, 330–332:
    independent laws of the original prime-ideal
    reduction model. Analytic representatives, equations,
    ideals and geometric conclusions are specified
    before the existence proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import Hom RealNormUP NormMetric LinearBasis GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness NormDifferentialUP NormAnalyticUP
  AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRing AnalyticPrefixGermMap
  AnalyticCoordinateSubringFamilySealed OrdinalCoordinateTail CommutativeIdealUP
  SetGermUP SetGermSealed IdealVarietyGermSealed FunctionalAnalyticSubmanifoldUP
  MetricSubsetBackground HomeomorphismUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Model.
Variable R:realType.
Variables n m:nat.
Hypothesis hMN:(m<=n)%N.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R m).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R m)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation Top:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation PY:=(@analytic_representative_type R Y NY hNY 0).
Local Notation PX:=(@analytic_representative_type R X NX hNX 0).
Local Notation vy:=(@analytic_representative_value R Y NY hNY 0).
Local Notation vx:=(@analytic_representative_value R X NX hNX 0).
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Variable omega:'I_n->Hom X R^o.
Variable P:Hom X Y.
Variable Ig:set G.
Variable hIg:is_finitely_generated_commutative_ideal Ig.
Variable k:nat.
Variable first:'I_(n-m).
Variable U:set Y.
Variable d:PY.
Variable b:'I_(n-m)->'I_k->PY.
Variable f:'I_(n-m)->PX.
Variable Z:set X.
Variable K:set G.
Variable hK:is_finitely_generated_commutative_ideal K.
Local Notation tail:=(ordinal_coordinate_tail_index hMN).
Local Notation xi:=(fun j:'I_(n-m)=>omega (tail j)).
Local Notation E:=(@analytic_prefix_germ_map R X NX hNX n e he omega m hMN).
Local Notation A:=(fun x:X=>U (P x)).
Local Notation V:=(fun y:Y=>U y /\vy d y!=0).

(** Source for [is_analytic_prime_local_model]:
    all original prime-ideal model assertions in
    3.4.8(10), pp. 327, 330–332.
    The defining functions and their germs
    refer to the same actual representatives.
    Compactness and finite-fibre bounds retain
    the subsidiary assertions on p. 332. *)
Definition is_analytic_prime_local_model:Prop:=
  (first:nat) = 0%N /\(0<k)%N /\U 0 /\@open (real_norm_metric_space hNY) U /\
  @norm_analytic R Y R^o NY (fun z:R^o=>`|z|) hNY (@scalar_absolute_value_norm R) U (vy d) /\
  (forall j i,@norm_analytic R Y R^o NY (fun z:R^o=>`|z|) hNY (@scalar_absolute_value_norm R) U (vy (b j i))) /\
  (forall j,@norm_analytic R X R^o NX (fun z:R^o=>`|z|) hNX (@scalar_absolute_value_norm R) A (vx (f j))) /\
  (forall i,vy (b first i) 0 = 0) /\
  (forall j x,vx (f j) x = if j==first then
    (xi first x)^+k+\sum_(i<k) vy (b first i) (P x)*(xi first x)^+(i:nat) else
    vy d (P x)*xi j x-\sum_(i<k) vy (b j i) (P x)*(xi first x)^+(i:nat)) /\
  (forall x,Z x <->A x /\(forall j,vx (f j) x = 0) /\vy d (P x)!=0) /\
  ~Ig (E (analytic_germ d)) /\(forall j,Ig (analytic_germ (f j))) /\
  is_generated_commutative_ideal (Ig `|` [set alpha:G|alpha = E (analytic_germ d)]) K /\
  @IdealVarietyGerm.value R X NX hNX 0 Ig hIg =
    @SetGerms.join Top 0 (@IdealVarietyGerm.value R X NX hNX 0 K hK) (@set_germ Top 0 Z) /\
  (forall x,Z x ->exists L:Hom X R^o,
    has_norm_differential NX (fun z:R^o=>`|z|) A (vx (f first)) x L /\L (e (tail first))!=0) /\
  is_functional_analytic_submanifold m A Z /\
  (forall C:set Y,compact [set y:real_norm_metric_space hNY|C y] ->C `<=` V ->
    compact [set x:real_norm_metric_space hNX|Z x /\C (P x)]) /\
  (forall y:Y,finite_set [set x|Z x /\P x = y] /\
    forall q:seq X,uniq q ->(forall x,x \in q ->Z x /\P x = y) ->(size q<=k)%N) /\
  (forall x,Z x ->exists F:metric_subset [set a:real_norm_metric_space hNX|
      @connected_component (real_norm_metric_space hNX) Z x a]->
    metric_subset [set y:real_norm_metric_space hNY|
      @connected_component (real_norm_metric_space hNY) V (P x) y],
    (forall a,val (F a) = P (val a)) /\is_homeomorphism F) /\
  forall H:set G,is_commutative_ideal H ->Ig `<=` H ->
    (exists alpha:G,H alpha /\~Ig alpha) ->exists beta:G,H beta /\
      @AnalyticCoordinateSubringFamily.value R X NX hNX n e he omega m beta /\~Ig beta /\beta<>0.
End Model.
