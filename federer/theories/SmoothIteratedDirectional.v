(** Federer (1969), 4.1.1, p. 346: repeated
    test differentiation uses the actual smooth
    derivatives already defined in 3.1.11, p. 223.
    This supporting theorem identifies compositions
    with that original recursive graph. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearOne NormHigherDifferentialUP NormHigherDifferentialFirst
  NormDifferentialLine NormIteratedDirectionalUP NormIteratedDirectionalLaws
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothDirectionalDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section IteratedSmoothDerivative.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:X->Prop.
Variable E:lmodType R.
Variable ev:E->X->Y.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Local Notation evZ := (fun k=>@ContinuousMultilinear.evaluation R k X Y NX NY hNX hNY).
Local Notation ZN := (fun k=>@ContinuousMultilinear.norm R k X Y NX NY hNX hNY).
Local Notation hZ := (fun k=>@ContinuousMultilinear.laws R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Variable P:X->Hom E E.
Hypothesis hP:forall v,@is_smooth_directional_derivative R X Y NX NY hNX hNY U E ev D v (P v).

(** Source for [smooth_iterated_directional_operator]:
    compose the actual directional derivatives in
    the order of the recursive convention in
    Federer 3.1.11, p. 223, used by
    4.1.1, p. 346. *)
Fixpoint smooth_iterated_directional_operator (s:seq X):Hom E E:=
  if s is v::t then hom_comp (P v) (smooth_iterated_directional_operator t)
  else hom_of_linear (linear_id E).

(** Source for [smooth_iterated_directional_graph]: the
    composition evaluates to the original iterated
    directional derivative graph, supporting the
    multiindex test operators of Federer 4.1.1,
    p. 346. No commutation assumption is added. *)
Theorem smooth_iterated_directional_graph s f a:
  U a ->has_norm_iterated_directional NY U (ev f) s a
    (ev (smooth_iterated_directional_operator s f) a).
Proof.
elim:s a=>[|v s ih] a ha; first by split.
pose g:=ev (smooth_iterated_directional_operator s f).
exists g; split.
- move=>x y hy.
  have hx:=norm_iterated_directional_domain hy.
  exact:(norm_iterated_directional_unique hNY (ih x hx) hy).
- have hFirst:=(@norm_higher_differential_first R X Y NX NY hNX hNY Z evZ ZN hZ
    U g a (@D 1%N a (smooth_iterated_directional_operator s f))).1
    (@smooth_derivative_exact R X Y NX NY hNX hNY U E ev D hD
      1%N (smooth_iterated_directional_operator s f) a ha).
  have hLine:=norm_differential_line hNX hNY hFirst v.
  have hValue:ev (smooth_iterated_directional_operator (v::s) f) a=
    @evZ 1%N [ffun _: 'I_1=>v] (@D 1%N a (smooth_iterated_directional_operator s f)).
    exact:(hP v _ ha).
  rewrite hValue; split; last exact:hLine.2.
  have [r [hr hLineDomain]]:=hLine.1.
  exists r; split=>// t ht.
  exists (g (a+t*:v)); exact:ih _ (hLineDomain t ht).
Qed.
End IteratedSmoothDerivative.
