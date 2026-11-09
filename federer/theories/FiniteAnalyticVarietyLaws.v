(** Federer (1969), 3.4.5, p. 320: finite
    analytic varieties are closed under the two printed
    operations and admit a single analytic defining equation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormClassZeroTopology NormBoundedLinearTopology
  NormAnalyticUP NormAnalyticScalarProducts FiniteAnalyticVarietyUP FiniteZeroSetSealed FiniteZeroSetLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Varieties.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable U:set X.
Local Notation AN f:=(@norm_analytic R X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R) U f).
Local Notation VAR S:=(@is_finite_analytic_variety R X NX hNX U S).
Local Notation zero I f:=(@FiniteZeroSet.value [the zmodType of R^o] X U I f).

(** Source for [finite_analytic_variety_union]: pairwise
    multiplication of actual analytic equations proves closure
    under union, 3.4.5, p. 320. *)
Lemma finite_analytic_variety_union (S T:set X):VAR S ->VAR T ->VAR (S `|` T).
Proof.
move=>[hU [I [f [hf hS]]]] [_ [J [g [hg hT]]]].
have hSEq:S=zero I f.
  apply/seteqP;split=>x;by rewrite (hS x) (original_zero_set_membership (FiniteZeroSet.laws _ f) x).
have hTEq:T=zero J g.
  apply/seteqP;split=>x;by rewrite (hT x) (original_zero_set_membership (FiniteZeroSet.laws _ g) x).
split;first exact:hU.
exists (Finite.clone (I*J)%type _),(fun ij x=>f ij.1 x*g ij.2 x);split.
- move=>[i j];exact:(@norm_analytic_scalar_product R X NX hNX U (f i) (g j) (hf i) (hg j)).
- move=>x;rewrite hSEq hTEq finite_zero_set_union.
  exact:(original_zero_set_membership (FiniteZeroSet.laws U _) x).
Qed.

(** Source for [finite_analytic_variety_intersection]: joining
    the original equations proves closure under intersection,
    3.4.5, p. 320. *)
Lemma finite_analytic_variety_intersection (S T:set X):VAR S ->VAR T ->VAR (S `&` T).
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

(** Source for [finite_analytic_variety_one_equation]: the
    sum of squares is an actual analytic defining function
    of the same original variety, 3.4.5, p. 320. *)
Lemma finite_analytic_variety_one_equation (S:set X):VAR S ->
  exists h:X->R,AN h /\forall x,S x <->U x /\h x=0.
Proof.
move=>[hU [I [f [hf hS]]]].
have hOpen x (hx:U x):norm_domain_interior NX U x.
  have hUNeighbourhood:=hU;rewrite openE in hUNeighbourhood.
  exact:((@norm_domain_interior_neighbourhood R X NX hNX U x).2 (hUNeighbourhood x hx)).
exists (fun x=>\sum_i (f i x)^+2);split.
- apply:(@norm_analytic_finite_scalar_sum R X NX hNX U I (fun i x=>(f i x)^+2) hOpen)=>i.
  exact:(@norm_analytic_scalar_power R X NX hNX U (f i) 2 (hf i)).
- move=>x.
  have hSEq:S=zero I f.
    apply/seteqP;split=>y;by rewrite (hS y) (original_zero_set_membership (FiniteZeroSet.laws _ f) y).
  rewrite hSEq finite_zero_set_sum_of_squares (original_zero_set_membership (FiniteZeroSet.laws _ _) x).
  split.
  + move=>[hx hZero];by split;last exact:hZero ord0.
  + move=>[hx hZero];by split.
Qed.
End Varieties.
