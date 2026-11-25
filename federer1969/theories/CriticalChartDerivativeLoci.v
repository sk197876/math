(** Federer (1969), 3.4.2(7), p. 312: the open complement of
    each derivative-vanishing condition defining the common set B. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormMetric RealNormUP NormDifferentialUP
  NormDifferentialLocal NormDifferentialDirectional NormClassOneUP NormRegularity RelativeClassUP
  NormClassZeroNonzeroLocus EuclideanProjectionSpace CriticalManifoldFamilyUP
  CriticalChartRetractionClass CriticalFieldVectorContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_chart_derivative_nonzero_locus]: supporting
    the closedness assertion for B in 3.4.2(7), p. 312. This is the
    locus where the genuine ambient derivative of f composed with r
    has a nonzero value on Z. The domain and derivative are explicit;
    no value is assigned where the derivative is undefined. *)
Definition critical_chart_derivative_nonzero_locus (R:realType) m mu
    (Y:lmodType R) (NY:Y->R) (Z:subspace (R_n R m)) (S:set (R_n R m))
    (p:euclidean_projection_space R m mu) (g:R_n R mu->R_n R m)
    (f:R_n R m->Y):set (R_n R m):=
  [set a|(euclidean_projection_linear p @` S) (euclidean_projection_linear p a) /\
    exists D:Hom (R_n R m) Y,
      has_norm_differential (inner_norm (@euclidean_inner_productP R m)) NY
        (fun x=>(euclidean_projection_linear p @` S) (euclidean_projection_linear p x))
        (fun x=>f (g (euclidean_projection_linear p x))) a D /\
      exists z,Z z /\D z!=0].

(** Source for [critical_chart_derivative_nonzero_open]: continuity
    of the derivative makes the complement of its vanishing tests
    open, as used for B in 3.4.2(7), p. 312. Uniqueness identifies
    every derivative witness with a local field representative;
    openness is independent of that representative. *)
Theorem critical_chart_derivative_nonzero_open (R:realType) m mu
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (Z:subspace (R_n R m)) (S:set (R_n R m))
    (p:euclidean_projection_space R m mu) g (f:R_n R m->Y):
  is_critical_manifold_chart 1 Z S p g ->
  norm_class_relative (inner_norm_real_norm (@euclidean_inner_productP R m))
    hNY S S f 1 ->
  @open (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)))
    (critical_chart_derivative_nonzero_locus NY Z S p g f).
Proof.
move=>hChart hf.
pose X:=R_n R m.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose U:=fun x=>(euclidean_projection_linear p @` S) (euclidean_projection_linear p x).
pose F:=fun x=>f (g (euclidean_projection_linear p x)).
have hF:=critical_chart_relative_composition_class hChart hf.
have [DF hDF]:=(norm_class_firstP hNX hNY U F).1 hF.
have hEqual:critical_chart_derivative_nonzero_locus NY Z S p g f=
    \bigcup_(z in Z) [set x|U x /\DF x z!=0].
  apply/seteqP;split.
  - move=>x [hxU [D [hD [z [hz hn]]]]].
    have hSame:D=DF x:=norm_differential_unique hNX hNY hD
      (norm_class_one_differential hDF hxU).
    exists z;first exact:hz.
    split;first exact:hxU.
    by rewrite -hSame.
  - move=>x [z hz [hxU hn]];split;first exact:hxU.
    exists (DF x);split;first exact:(norm_class_one_differential hDF hxU).
    by exists z.
rewrite hEqual;apply:bigcup_open=>z hz.
apply:(@norm_class_zero_nonzero_locus_open R X Y NX NY hNX hNY U (fun x=>DF x z)).
exact:(@critical_derivative_vector_class_zero R X Y NX NY hNX U F DF z hDF).
Qed.
