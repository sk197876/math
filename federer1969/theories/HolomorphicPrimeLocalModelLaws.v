(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), pp. 327, 331–332:
    public consequences of the independent
    actual local-model laws. All ideal
    and variety statements refer to the
    original representative and germ data. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom RealNormUP NormMetric LinearBasis GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness NormDifferentialUP HolomorphicUP
  HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRing HolomorphicPrefixGermMap
  HolomorphicCoordinateSubringFamilySealed OrdinalCoordinateTail CommutativeIdealUP
  SetGermUP SetGermSealed HolomorphicIdealVarietyGermSealed FunctionalHolomorphicSubmanifoldUP
  MetricSubsetBackground HomeomorphismUP HolomorphicPrimeLocalModelUP.
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

Hypothesis hModel:@is_holomorphic_prime_local_model R n m hMN e he omega P Ig hIg k first U d b f Z K hK.

(** Source for [holomorphic_prime_local_model_delta_outside]:
    the original denominator germ lies outside
    I_g, 3.4.12, p. 339, extending 3.4.8(10), pp. 327, 331. *)
Lemma holomorphic_prime_local_model_delta_outside:
  ~Ig (E (holomorphic_germ d)).
Proof. exact:hModel.2.2.2.2.2.2.2.2.2.2.1. Qed.

(** Source for [holomorphic_prime_local_model_enlarged_ideal]:
    the enlarged ideal contains I_g and
    the original denominator, 3.4.12, p. 339, extending 3.4.8(10),
    pp. 330–331. *)
Lemma holomorphic_prime_local_model_enlarged_ideal:
  is_generated_commutative_ideal (Ig `|` [set alpha:G|alpha = E (holomorphic_germ d)]) K.
Proof. exact:hModel.2.2.2.2.2.2.2.2.2.2.2.2.1. Qed.

(** Source for [holomorphic_prime_local_model_variety]:
    the exact original decomposition of var(I_g),
    3.4.12, p. 339, extending 3.4.8(10), pp. 327, 331–332. *)
Lemma holomorphic_prime_local_model_variety:
  @HolomorphicIdealVarietyGerm.value R X NX hNX 0 Ig hIg =
    @SetGerms.join Top 0 (@HolomorphicIdealVarietyGerm.value R X NX hNX 0 K hK) (@set_germ Top 0 Z).
Proof. exact:hModel.2.2.2.2.2.2.2.2.2.2.2.2.2.1. Qed.

End Model.
