(** Federer (1969), 3.4.8(10), pp. 327, 331–332:
    public consequences of the independent
    actual local-model laws. All ideal
    and variety statements refer to the
    original representative and germ data. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import Hom RealNormUP NormMetric LinearBasis GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness NormDifferentialUP NormAnalyticUP
  AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRing AnalyticPrefixGermMap
  AnalyticCoordinateSubringFamilySealed OrdinalCoordinateTail CommutativeIdealUP
  SetGermUP SetGermSealed IdealVarietyGermSealed FunctionalAnalyticSubmanifoldUP
  MetricSubsetBackground HomeomorphismUP AnalyticPrimeLocalModelUP.
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

Hypothesis hModel:@is_analytic_prime_local_model R n m hMN e he omega P Ig hIg k first U d b f Z K hK.

(** Source for [analytic_prime_local_model_delta_outside]:
    the original denominator germ lies outside
    I_g, 3.4.8(10), pp. 327, 331. *)
Lemma analytic_prime_local_model_delta_outside:
  ~Ig (E (analytic_germ d)).
Proof. exact:hModel.2.2.2.2.2.2.2.2.2.2.1. Qed.

(** Source for [analytic_prime_local_model_enlarged_ideal]:
    the enlarged ideal contains I_g and
    the original denominator, 3.4.8(10),
    pp. 330–331. *)
Lemma analytic_prime_local_model_enlarged_ideal:
  is_generated_commutative_ideal (Ig `|` [set alpha:G|alpha = E (analytic_germ d)]) K.
Proof. exact:hModel.2.2.2.2.2.2.2.2.2.2.2.2.1. Qed.

(** Source for [analytic_prime_local_model_variety]:
    the exact original decomposition of var(I_g),
    3.4.8(10), pp. 327, 331–332. *)
Lemma analytic_prime_local_model_variety:
  @IdealVarietyGerm.value R X NX hNX 0 Ig hIg =
    @SetGerms.join Top 0 (@IdealVarietyGerm.value R X NX hNX 0 K hK) (@set_germ Top 0 Z).
Proof. exact:hModel.2.2.2.2.2.2.2.2.2.2.2.2.2.1. Qed.

End Model.
