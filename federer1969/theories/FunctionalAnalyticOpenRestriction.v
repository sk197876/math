(** Federer (1969), 3.4.8(11), pp. 334–335:
    the original functional analytic regular part
    restricts to the selected open neighbourhood.
    Retain its defining equations, nonvanishing function
    and actual independent differentials. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormDifferentialUP NormDifferentialLocal NormBoundedLinearTopology
  NormAnalyticUP NormAnalyticOperations FunctionalAnalyticSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [functional_analytic_open_restriction]:
    S=D intersect V is a functional
    analytic m-submanifold of V, used
    in 3.4.8(11), p. 335. *)
Theorem functional_analytic_open_restriction (R:realType) n m
    (U V S:set (R_n R n)):
  @is_functional_analytic_submanifold R n m U S ->
  @open (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) V ->
  V `<=` U ->
  @is_functional_analytic_submanifold R n m V (V `&` S).
Proof.
move=>[hMN [hU [f [g [hF [hG [hEquation hDifferentials]]]]]]] hV hVU.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
have hInterior x (hx:V x):norm_domain_interior NX V x.
  have hOpen:=hV;rewrite openE in hOpen.
  exact:(@norm_domain_interior_neighbourhood R X NX hNX V x).2 (hOpen x hx).
split;first exact:hMN.
split;first exact:hV.
exists f,g;split.
- move=>i;exact:(@norm_analytic_open_restriction R X R^o NX (fun z:R^o=>`|z|)
    hNX (@scalar_absolute_value_norm R) U V (f i) hVU hInterior (hF i)).
- split.
  + exact:(@norm_analytic_open_restriction R X R^o NX (fun z:R^o=>`|z|)
      hNX (@scalar_absolute_value_norm R) U V g hVU hInterior hG).
  + split.
    * move=>x;split.
      -- move=>[hx /hEquation [_ hRest]];by split.
      -- move=>[hx hRest];split;first exact:hx.
         apply/(hEquation x);split;[exact:hVU x hx|exact:hRest].
    * move=>x [hx hSx];have [D [hD hIndependent]]:=hDifferentials x hSx.
      exists D;split;last exact:hIndependent.
      move=>i;exact:(@norm_differential_restrict R X R^o NX (fun z:R^o=>`|z|)
        U V (f i) x (D i) hVU (hInterior x hx) (hD i)).
Qed.
