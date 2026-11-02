(** Federer (1969), 3.2.11, p. 249: the
    actual differential of g(x,z)=f(x)+epsilon*z and its
    full-rank locus. Expand the printed differentiation with
    the project's linear, chain, sum and scalar rules. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness EuclideanBlockLinearMaps CoareaPerturbationMap CoareaPerturbationLinear
  CoareaPerturbationBound CoordinateInverseCoverUP NormDifferentialUP NormDifferentialLinear
  NormDifferentialChain NormDifferentialArithmetic NormDifferentialLocal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coarea_perturbation_differential]: the
    differential formula in Federer 3.2.11, p. 249.
    At every actual differentiability point of f in
    the first block, the perturbation has the prescribed
    differential Dg(v,w)=Df(v)+epsilon*w. No derivative default
    or independent differentiability assumption on g is used. *)
Theorem coarea_perturbation_differential (R:realType) m n
    (f:R_n R m->R_n R n) e (w:R_n R (m+n))
    (D:Hom (R_n R m) (R_n R n)):
  has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f
    (@euclidean_first_block R m n w) D ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R (m+n)))
    (inner_norm (@euclidean_inner_productP R n)) setT
    (coarea_perturbation_map f e) w (coarea_perturbation_linear D e).
Proof.
move=>hD.
pose NX:=inner_norm (@euclidean_inner_productP R (m+n)).
pose NM:=inner_norm (@euclidean_inner_productP R m).
pose NY:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R (m+n)).
pose hNM:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose p:=@euclidean_first_block_map R m n.
pose q:=@euclidean_last_block_map R m n.
have hWhole:norm_domain_interior NX setT w.
  exists 1; split; first exact:ltr01; by move=>h hh.
have hP:norm_bounded_linear NX NM p.
  exists 1; split; first exact:ler01.
  move=>x; rewrite mul1r; exact (@coarea_block_projection_norms R m n x).1.
have hQ:norm_bounded_linear NX NY q.
  exists 1; split; first exact:ler01.
  move=>x; rewrite mul1r; exact (@coarea_block_projection_norms R m n x).2.
have hPDiff:=norm_differential_linear hNX hNM hWhole hP.
have hChain:=norm_differential_chain hNX hNM hNY hPDiff hD.
have hFirst:=norm_differential_restrict (fun x _=>conj Logic.I Logic.I) hWhole hChain.
have hQDiff:=norm_differential_linear hNX hNY hWhole hQ.
have hScale:=@norm_differential_scale R (R_n R (m+n)) (R_n R n)
  NX NY hNX hNY setT q w q e hQDiff.
have hSum:=norm_differential_add hNY hFirst hScale.
exact hSum.
Qed.

(** Source for [coarea_perturbation_full_rank]: im Dg=R^n
    in Federer 3.2.11, p. 249. Every source point
    whose first block has an actual differential of f
    lies in g's actual full-rank locus when epsilon is nonzero. *)
Lemma coarea_perturbation_full_rank (R:realType) m n
    (f:R_n R m->R_n R n) e (w:R_n R (m+n)):
  e!=0 ->norm_differentiable_at (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f (@euclidean_first_block R m n w) ->
  surjective_differential_locus (coarea_perturbation_map f e) w.
Proof.
move=>he [D hD]; exists (coarea_perturbation_linear D e); split.
- exact (@coarea_perturbation_differential R m n f e w D hD).
- exact (coarea_perturbation_linear_surjective D he).
Qed.
