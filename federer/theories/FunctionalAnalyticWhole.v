(** Federer (1969), 3.4.5, p. 321, and
    3.4.8(16), p. 337: the whole Euclidean
    space is a functional analytic submanifold of its
    full dimension. The defining equation family is empty. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormDifferentialUP NormAnalyticUP NormAnalyticConstant
  NormOpenDomainLaws FiniteIndependence FunctionalAnalyticSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [functional_analytic_whole]: the empty-equation,
    full-dimensional case of 3.4.5, p. 321,
    used at the full-dimensional endpoint of
    3.4.8(16), p. 337. Dimension zero remains. *)
Theorem functional_analytic_whole (R:realType) n:
  @is_functional_analytic_submanifold R n n setT setT.
Proof.
pose X:=R_n R n;pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
have hNoIndex (i:'I_(n-n)):False.
  case:i=>j hj.
  by move:hj;rewrite subnn ltn0.
split;first exact:leqnn.
split;first exact:openT.
exists (fun (i:'I_(n-n)) (x:X)=>(0:R)),(fun (x:X)=>(1:R));split.
- move=>i;exact:False_ind _ (hNoIndex i).
split.
- exact:(@norm_constant_analytic R X R^o NX (fun z:R^o=>`|z|) hNX (@scalar_absolute_value_norm R)
    setT (fun x _=>norm_full_domain_interior NX x) 1).
split.
- move=>x;split;last by move=>_.
  move=>_;split;first exact:Logic.I.
  split;first by move=>i;exact:False_ind _ (hNoIndex i).
  by move/eqP;rewrite oner_eq0.
- move=>x hx;exists (fun i:'I_(n-n)=>(0:Hom X R^o));split.
  + move=>i;exact:False_ind _ (hNoIndex i).
  + move=>c hC i;exact:False_ind _ (hNoIndex i).
Qed.
