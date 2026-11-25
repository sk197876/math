(** Federer (1969), 4.1.26, p. 383: the
    original signed determinant sum over A intersected
    with the literal fibre. This equivalent graph
    formula retains critical differentiability points,
    permits arbitrary source sets, and assigns no
    value at undefined or infinite sums. Almost-
    everywhere existence is proved separately. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps
  ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPostcomposition
  PartialFibreNumericalSum NumericalSum NumericalSumValues NumericalSumZeroOffSet
  LipschitzDegreeSummandUP LipschitzDegreeSummandSealed LipschitzDegreeUP LipschitzDegreeSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lipschitz_degree_fibre_graph]: the
    displayed determinant-sign sum in 4.1.26,
    p. 383. The current definition by zero
    extension is equivalent to this exact original
    restricted fibre, without a differential premise
    at points outside A. *)
Theorem lipschitz_degree_fibre_graph (R:realType) m
    (f:R_n R m->R_n R m) (A:set (R_n R m)) y a:
  partial_function_graph (@LipschitzDegree.value R m f A) y a<->
  exists w:R_n R m->R,
    (forall x,A x->f x=y->exists D:Hom (R_n R m) (R_n R m),
      has_norm_differential (inner_norm (@euclidean_inner_productP R m))
        (inner_norm (@euclidean_inner_productP R m)) (fun _=>True) f x D /\
      Num.sg (@euclidean_det R m (hom_as_linear D))=w x) /\
    numerical_sum (A `&` [set x|f x=y]) (fun x=>(w x)%:E)=Some a%:E.
Proof.
rewrite (@LipschitzDegree.laws R m f A y a)
  partial_fibre_numerical_sum_graph;split.
- move=>[v [hOn hSum]].
  pose w:=fun x=>fine (v x).
  have hReal:forall x,f x=y->v x=(w x)%:E.
    move=>x hx;have[b [hB hValue]]:=hOn x hx.
    by rewrite /w -hValue.
  have hOff:forall x,f x=y->~A x->v x=0%E.
    move=>x hx hAx;have[b [hB hValue]]:=hOn x hx.
    have hZero:partial_function_graph (@LipschitzDegreeSummand.value R m f A) x 0.
      apply:(@LipschitzDegreeSummand.laws R m f A x 0).2;left;by split.
    have hb:b=0:=partial_function_single_valued hB hZero.
    by rewrite -hValue hb.
  exists w;split.
  + move=>x hAx hx;have[b [hB hValue]]:=hOn x hx.
    have [[hNot _]|[_ [D [hD hSign]]]]:=
      (@LipschitzDegreeSummand.laws R m f A x b).1 hB.
    * by case:(hNot hAx).
    * exists D;split;first exact:hD.
      by rewrite /w -hValue.
  + have hRestricted:=numerical_sum_zero_off_set hOff.
    have hValues:numerical_sum ([set x|f x=y] `&` A) v=
        numerical_sum ([set x|f x=y] `&` A) (fun x=>(w x)%:E).
      apply:numerical_sum_ext=>x [hx _];exact:hReal x hx.
    by rewrite setIC -hValues -hRestricted.
- move=>[w [hOn hSum]].
  pose v:=fun x=>if x \in A then (w x)%:E else 0%E.
  exists v;split.
  + move=>x hx;case:(pselect (A x))=>hAx.
    * rewrite /v (mem_set hAx).
      exists (w x);split;last reflexivity.
      apply:(@LipschitzDegreeSummand.laws R m f A x (w x)).2.
      right;split;first exact:hAx;exact:hOn x hAx hx.
    * have hNot:x \notin A by apply/negP=>/set_mem h;exact:hAx h.
      rewrite /v (negbTE hNot).
      exists 0;split;last reflexivity.
      apply:(@LipschitzDegreeSummand.laws R m f A x 0).2.
      left;by split.
  + have hOff:forall x,f x=y->~A x->v x=0%E.
      move=>x _ hx.
      have hNot:x \notin A by apply/negP=>/set_mem h;exact:hx h.
      by rewrite /v (negbTE hNot).
    rewrite (numerical_sum_zero_off_set hOff) setIC.
    have hValues:numerical_sum (A `&` [set x|f x=y]) v=
        numerical_sum (A `&` [set x|f x=y]) (fun x=>(w x)%:E).
      apply:numerical_sum_ext=>x [hx _];by rewrite /v (mem_set hx).
    by rewrite hValues.
Qed.
