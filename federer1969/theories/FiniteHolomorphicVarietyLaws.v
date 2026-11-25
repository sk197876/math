(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 320: finite
    analytic varieties are closed under the two printed
    operations and admit a single analytic defining equation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import HolomorphicUP FiniteAnalyticVarietyUP ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP NormMetric NormDifferentialUP NormClassZeroTopology NormBoundedLinearTopology
  NormAnalyticUP HolomorphicProduct FiniteHolomorphicVarietyUP FiniteZeroSetSealed FieldFiniteZeroSetLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Varieties.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Hypothesis hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX.
Variable U:set X.
Local Notation HOL f:=(@is_holomorphic R X (ComplexScalars.C R)^o NX (@complex_modulus R) hNX (@complex_modulus_real_norm R) U f).
Local Notation VAR S:=(@is_finite_holomorphic_variety R X NX hNX U S).
Local Notation zero I f:=(@FiniteZeroSet.value [the zmodType of (ComplexScalars.C R)^o] X U I f).

(** Source for [finite_holomorphic_variety_union]: pairwise
    multiplication of actual analytic equations proves closure
    under union, 3.4.5, p. 320. *)
Lemma finite_holomorphic_variety_union (S T:set X):VAR S ->VAR T ->VAR (S `|` T).
Proof.
move=>[hU [I [f [hf hS]]]] [_ [J [g [hg hT]]]].
have hSEq:S=zero I f.
  apply/seteqP;split=>x;by rewrite (hS x) (original_zero_set_membership (FiniteZeroSet.laws _ f) x).
have hTEq:T=zero J g.
  apply/seteqP;split=>x;by rewrite (hT x) (original_zero_set_membership (FiniteZeroSet.laws _ g) x).
split;first exact:hU.
exists (Finite.clone (I*J)%type _),(fun ij x=>f ij.1 x*g ij.2 x);split.
- move=>[i j];exact:(@holomorphic_product R X NX hNX U (f i) (g j) (hf i) (hg j)).
- move=>x;rewrite hSEq hTEq field_finite_zero_set_union.
  exact:(original_zero_set_membership (FiniteZeroSet.laws U _) x).
Qed.

(** Source for [finite_holomorphic_variety_intersection]: joining
    the original equations proves closure under intersection,
    3.4.5, p. 320. *)
Lemma finite_holomorphic_variety_intersection (S T:set X):VAR S ->VAR T ->VAR (S `&` T).
Proof.
move=>[hU [I [f [hf hS]]]] [_ [J [g [hg hT]]]].
split;first exact:hU.
exists (Finite.clone (I+J)%type _),(fun ij=>match ij with inl i=>f i|inr j=>g j end);split.
- by move=>[i|j];[exact:hf i|exact:hg j].
- move=>x;split.
  + move=>[/hS [hx hF] /hT [_ hG]];split;first exact:hx.
    by move=>[i|j];[exact:hF i|exact:hG j].
  + move=>[hx hZero];split;[apply/(hS x)|apply/(hT x)];split;first exact:hx.
    * move=>i;exact:hZero (inl i).
    * exact:hx.
    * move=>j;exact:hZero (inr j).
Qed.

End Varieties.
