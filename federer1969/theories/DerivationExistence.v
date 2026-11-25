(** Federer (1969), 2.9.5, pp. 154–155: the V derivate of psi with respect
    to phi exists and is finite nonnegative phi almost everywhere. The proof
    removes the printed three kinds of exceptional sets and uses countably
    many positive rational gaps. The stronger supporting conclusion also
    excludes fine null-cell fibers; the numbered theorem retains Federer's
    exact value assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import MeasureDerivationContext MeasureDerivates PartialFunctionUP
  CoveringRelationUP CoveringRelationLimits MeasureUP MeasureAlmostUP MeasureAlmostBasic
  DerivationRatioDomain VitaliNullFibers DerivationExceptionalSets DerivationRationalGaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_derivate_exists_ae]: supporting strengthened domain
    assertion in the proof of Federer 2.9.5, pp. 154–155 Almost every point
    lies outside P and has a defined finite nonnegative derivate. The
    original M supplies both measures' bounded finiteness. *)
Theorem measure_derivate_exists_ae (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop) :
  is_measure_derivation_context phi V -> is_derivation_measure psi ->
  measure_almost_everywhere phi [set x |
    ~ covering_relation_fine_at (fun x S => V x S /\ phi S=0) x /\
    exists y, partial_function_graph (measure_derivate psi phi V) x y /\ 0<=y /\ y< +oo].
Proof.
move=> hc hp.
have hf := derivation_context_measure hc.
have hm := derivation_measure_law hf.
have hv := derivation_context_vitali hc.
pose P := [set x | covering_relation_fine_at (fun x S => V x S /\ phi S=0) x].
pose Q := derivation_infinite_upper_points psi phi V.
pose D := positive_rational_gaps R.
pose F (p : rat*rat) := derivation_gap_points psi phi V (ratr p.1 : R) (ratr p.2 : R).
pose N := \bigcup_(p in D) F p.
have hP : phi P=0 := @vitali_null_fine_points_null R X phi V hm hv.
have hQ : phi Q=0 := @derivation_infinite_upper_points_null R X phi psi V hc hp.
have hN : phi N=0.
  apply: (@measure_null_countable_union R X _ phi hm D F (countableP _))=> p [ha hab].
  exact (@derivation_gap_points_null R X phi psi V (ratr p.1 : R) (ratr p.2 : R) hc hp ha hab).
have hQN : phi (Q `|` N)=0 := @measure_null_union R X phi hm Q N hQ hN.
have hE : phi (P `|` (Q `|` N))=0 := @measure_null_union R X phi hm P (Q `|` N) hP hQN.
apply: (@measure_null_subset R X phi hm _ (P `|` (Q `|` N))) hE.
move=> x hbad; apply: contrapT=> hnE; apply: hbad.
have hnP : ~ P x by move=> hx; apply: hnE; left.
have hnQ : ~ Q x by move=> hx; apply: hnE; right; left.
have hnN : ~ N x by move=> hx; apply: hnE; right; right.
split=> //.
pose f := measure_ratio_function psi phi.
pose l := covering_lower_limit V f x.
pose u := covering_upper_limit V f x.
have hdomain := @derivation_ratio_domain_fine R X psi phi V x hf (vitali_relation_fine hv x) hnP.
have hlu : l<=u := @covering_limits_ordered R X V f x hdomain.
have hl0 : 0<=l := @measure_ratio_lower_limit_nonnegative R X psi phi V x (derivation_measure_law hp) hm.
have huf : u< +oo.
  rewrite lt_def leey andbT; apply/eqP=> he; apply: hnQ; exact: esym he.
have heq : l=u.
  apply/eqP; rewrite eq_le hlu /= leNgt; apply/negP=> hgap.
  have [p [hpD [hla hbu]]] := @positive_rational_gap_between R l u hl0 hgap.
  apply: hnN; exists p=> //; by split.
exists u; split.
- split; first exact: vitali_relation_fine hv x.
  by split=> //; exact heq.
- split; [exact: le_trans hl0 hlu|exact huf].
Qed.

(** Source for [federer_2_9_5]: direct complete theorem
    Federer 2.9.5, pp. 154–155: 0<=D(psi,phi,V,x)<infinity
    for phi almost all x. Existence is expressed by
    a graph witness, so undefined derivatives are included
    in the exceptional null set rather than assigned a
    default value. *)
Theorem federer_2_9_5 (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop) :
  is_measure_derivation_context phi V -> is_derivation_measure psi ->
  measure_almost_everywhere phi [set x | exists y,
    partial_function_graph (measure_derivate psi phi V) x y /\ 0<=y /\ y< +oo].
Proof.
move=> hc hp.
apply: (@measure_almost_everywhere_mono R X phi (derivation_measure_law (derivation_context_measure hc))
  [set x | ~ covering_relation_fine_at (fun x S => V x S /\ phi S=0) x /\
    exists y, partial_function_graph (measure_derivate psi phi V) x y /\ 0<=y /\ y< +oo]).
- by move=> x [_ h].
- exact (@measure_derivate_exists_ae R X phi psi V hc hp).
Qed.
