(** Federer (1969), 3.1.22, p. 236: relative class k
    is equivalent to one ambient extension on an open neighbourhood;
    for a closed subset the extension can be global. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  InnerMetric HilbertFormCompactness InnerNormTopologyAdapters NormMetric NormDifferentialUP NormBoundedLinearTopology
  NormRegularity NormRegularityOperations RelativeClassUP EuclideanRelativeCoverExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [euclidean_relative_class_extension]: the full
    single-extension equivalence in Federer 3.1.22, p. 236.
    Its proof uses 3.1.13 as in the book, for any normed
    target, including class zero as a harmless strengthening. *)
Theorem euclidean_relative_class_extension (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (A S:set (R_n R n)) (f:R_n R n->Y) k :
  @norm_class_relative R (R_n R n) Y (inner_norm (@euclidean_inner_productP R n)) NY
    (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY A S f k <->
  exists U g,@is_norm_relative_extension R (R_n R n) Y
    (inner_norm (@euclidean_inner_productP R n)) NY
    (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY A S f k U g.
Proof.
split; last by move=>[U [g hg]]; exact: norm_relative_extension_class hg.
move=>hf.
pose X:=R_n R n.
pose M:=inner_metric_space (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose Phi:set (set M):=fun T=>exists g,norm_class hNX hNY T g k /\
  forall x,S x -> T x -> A x /\ f x=g x.
have hSU:S `<=` (\bigcup_(T in Phi) T).
  move=>a ha; have [T [g [haT [hg hag]]]]:=hf a ha.
  exists T=>//; by exists g.
have [g hg]:=@euclidean_relative_cover_extension R n Y NY hNY A S f k Phi
  (fun T hT=>hT) hSU.
exists (\bigcup_(T in Phi) T),g; exact hg.
Qed.

(** Source for [euclidean_closed_relative_class_extension]: the
    closed-subset global extension assertion of Federer 3.1.22,
    p. 236. The book cites 3.1.14; here the same
    3.1.13 gluing argument is applied after adjoining the
    open complement of S with its zero local extension.
    This proof-route departure avoids imposing target completeness. *)
Theorem euclidean_closed_relative_class_extension (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (A S:set (R_n R n)) (f:R_n R n->Y) k :
  @closed (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) S ->
  @norm_class_relative R (R_n R n) Y (inner_norm (@euclidean_inner_productP R n)) NY
    (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY A S f k ->
  exists g,@is_norm_relative_extension R (R_n R n) Y
    (inner_norm (@euclidean_inner_productP R n)) NY
    (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY A S f k setT g.
Proof.
move=>hS hf.
pose X:=R_n R n.
pose M:=inner_metric_space (@euclidean_inner_productP R n).
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose Phi:set (set M):=fun T=>exists g,norm_class hNX hNY T g k /\
  forall x,S x -> T x -> A x /\ f x=g x.
have hSC:Phi (~` S).
  exists (fun _=>0); split.
  - apply: norm_class_constant=>x hx.
    exact ((@norm_domain_interior_neighbourhood R X NX hNX (~` S) x).2
      (open_nbhs_nbhs (conj (closed_openC hS) hx))).
  - by move=>x hx hn; case: (hn hx).
have hU:(\bigcup_(T in Phi) T)=setT.
  apply/seteqP; split; first by move=>x _.
  move=>x _; case:(pselect (S x))=>[hx|hx].
  - have [T [g [hxT [hg hag]]]]:=hf x hx.
    exists T=>//; by exists g.
  - by exists (~` S).
have hSU:S `<=` (\bigcup_(T in Phi) T) by rewrite hU.
have [g hg]:=@euclidean_relative_cover_extension R n Y NY hNY A S f k Phi
  (fun T hT=>hT) hSU.
exists g; by rewrite -hU.
Qed.
