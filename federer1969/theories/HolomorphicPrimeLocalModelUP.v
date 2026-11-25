(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), pp. 327, 330–332:
    independent laws of the original prime-ideal
    reduction model. Holomorphic representatives, equations,
    ideals and geometric conclusions are specified
    before the existence proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric LinearBasis GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness NormDifferentialUP HolomorphicUP
  HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRing HolomorphicPrefixGermMap
  HolomorphicCoordinateSubringFamilySealed OrdinalCoordinateTail CommutativeIdealUP
  SetGermUP SetGermSealed HolomorphicIdealVarietyGermSealed FunctionalHolomorphicSubmanifoldUP
  HolomorphicFiniteCoverUP.
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
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation Y:=(coordinate_space (ComplexScalars.C R) m).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation NY:=(@holomorphic_coordinate_norm R m).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation hNY:=(complex_norm_real (@holomorphic_coordinate_norm_laws R m)).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation YR:=(restricted_space (ComplexScalars.embed R) Y).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o).
Local Notation Top:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)].
Local Notation PY:=(@holomorphic_representative_type R Y NY hNY 0).
Local Notation PX:=(@holomorphic_representative_type R X NX hNX 0).
Local Notation vy:=(@holomorphic_representative_value R Y NY hNY 0).
Local Notation vx:=(@holomorphic_representative_value R X NX hNX 0).
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
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
Local Notation E:=(@holomorphic_prefix_germ_map R X NX hNX n e he omega m hMN).
Local Notation A:=(fun x:X=>U (P x)).
Local Notation V:=(fun y:Y=>U y /\vy d y!=0).

(** Source for [is_holomorphic_prime_local_model]:
    all original prime-ideal model assertions in
    3.4.12, p. 339, extending 3.4.8(10), pp. 327, 330–332.
    The defining functions and their germs
    refer to the same actual representatives.
    Compactness and finite-fibre bounds retain
    the subsidiary assertions on p. 332. *)
Definition is_holomorphic_prime_local_model:Prop:=
  (first:nat) = 0%N /\(0<k)%N /\U 0 /\@open (real_norm_metric_space hNY) U /\
  @is_holomorphic R Y (ComplexScalars.C R)^o NY (@complex_modulus R) hNY (@complex_modulus_real_norm R) U (vy d) /\
  (forall j i,@is_holomorphic R Y (ComplexScalars.C R)^o NY (@complex_modulus R) hNY (@complex_modulus_real_norm R) U (vy (b j i))) /\
  (forall j,@is_holomorphic R X (ComplexScalars.C R)^o NX (@complex_modulus R) hNX (@complex_modulus_real_norm R) A (vx (f j))) /\
  (forall i,vy (b first i) 0 = 0) /\
  (forall j x,vx (f j) x = if j==first then
    (xi first x)^+k+\sum_(i<k) vy (b first i) (P x)*(xi first x)^+(i:nat) else
    vy d (P x)*xi j x-\sum_(i<k) vy (b j i) (P x)*(xi first x)^+(i:nat)) /\
  (forall x,Z x <->A x /\(forall j,vx (f j) x = 0) /\vy d (P x)!=0) /\
  ~Ig (E (holomorphic_germ d)) /\(forall j,Ig (holomorphic_germ (f j))) /\
  is_generated_commutative_ideal (Ig `|` [set alpha:G|alpha = E (holomorphic_germ d)]) K /\
  @HolomorphicIdealVarietyGerm.value R X NX hNX 0 Ig hIg =
    @SetGerms.join Top 0 (@HolomorphicIdealVarietyGerm.value R X NX hNX 0 K hK) (@set_germ Top 0 Z) /\
  (forall x,Z x ->exists L:Hom XR CR,
    @has_norm_differential R XR CR NX (@complex_modulus R) A (vx (f first)) x L /\L (e (tail first))!=0) /\
  is_functional_holomorphic_submanifold m A Z /\
  (forall C:set Y,compact [set y:real_norm_metric_space hNY|C y] ->C `<=` V ->
    compact [set x:real_norm_metric_space hNX|Z x /\C (P x)]) /\
  (forall y:Y,finite_set [set x|Z x /\P x = y] /\
    forall q:seq X,uniq q ->(forall x,x \in q ->Z x /\P x = y) ->(size q<=k)%N) /\
  @is_finite_holomorphic_projection_cover R X Y NX NY hNX hNY Z V P k /\
  forall H:set G,is_commutative_ideal H ->Ig `<=` H ->
    (exists alpha:G,H alpha /\~Ig alpha) ->exists beta:G,H beta /\
      @HolomorphicCoordinateSubringFamily.value R X NX hNX n e he omega m beta /\~Ig beta /\beta<>0.
End Model.
