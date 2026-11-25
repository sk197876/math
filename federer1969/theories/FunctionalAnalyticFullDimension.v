(** Federer (1969), 3.4.5, p. 321: the
    explicit n=m convention for functional analytic submanifolds
    leaves only the original nonvanishing inequality. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP Hom FiniteIndependence GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormMetric NormAnalyticUP FunctionalAnalyticSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [functional_analytic_full_dimension]: in
    case n=m the original S is precisely U minus the
    zero set of one analytic g, 3.4.5, p. 321. *)
Lemma functional_analytic_full_dimension (R:realType) n (U S:set (R_n R n)):
  is_functional_analytic_submanifold n U S <->
  @open (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) U /\
  exists g:R_n R n->R,
    @norm_analytic R (R_n R n) R^o (inner_norm (@euclidean_inner_productP R n))
      (fun z:R^o=>`|z|) (inner_norm_real_norm (@euclidean_inner_productP R n))
      (@scalar_absolute_value_norm R) U g /\forall x,S x <->U x /\g x<>0.
Proof.
have hEmpty (i:'I_(n-n)):False.
  have hBound:(n-n<=0)%N by rewrite subnn.
  have hh:=leq_trans (ltn_ord i) hBound.
  by move:hh;rewrite ltn0.
split.
- move=>[_ [hU [f [g [hf [hg [hS hD]]]]]]].
  split;first exact:hU.
  exists g;split;first exact:hg.
  move=>x;rewrite hS;split.
  + by move=>[hx [_ hNonzero]];split.
  + move=>[hx hNonzero];split;first exact:hx.
    split;last exact:hNonzero.
    move=>i;exfalso;exact:hEmpty i.
- move=>[hU [g [hg hS]]].
  split;first exact:leqnn.
  split;first exact:hU.
  exists (fun (_:'I_(n-n)) (_:R_n R n)=>(0:R)),g;split.
  + move=>i;exfalso;exact:hEmpty i.
  + split;first exact:hg.
    split.
    * move=>x;rewrite hS;split.
      -- move=>[hx hNonzero];split;first exact:hx.
         split;last exact:hNonzero.
         move=>i;exfalso;exact:hEmpty i.
      -- by move=>[hx [_ hNonzero]];split.
    * move=>x hx;exists (fun _=>0);split.
      -- move=>i;exfalso;exact:hEmpty i.
      -- move=>c hc i;exfalso;exact:hEmpty i.
Qed.
