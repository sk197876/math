(** Federer (1969), 4.1.14, p. 371: the weights
    h(g_i(x))(sigma(x)+eta_i)^m converge uniformly on K
    to h(f(x))sigma(x)^m. Regard the two scalar arguments
    as one continuous function on the product target.
    This retains degree zero and needs no positive lower
    bound for sigma. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealMetricBackground MetricProductBackground
  TopologicalProductMaps MetricCompactUniformComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_weighted_image_uniform]: the original
    smooth approximation weights converge uniformly on the original
    compact support, supporting Federer 4.1.14, p. 371.
    Only the actual image values are used, so an empty target
    never requires a selected point or extension. *)
Theorem compact_weighted_image_uniform (R:realType) (A:choiceType)
    (Y:metricType R) (K:set A) (f:A->Y) (g:nat->A->Y)
    (sigma:A->R^o) (eta:nat->R) (h:Y->R^o) (m:nat):
  compact ((fun x=>(f x,sigma x)) @` K:
    set (metric_product Y (real_line_metric R)))->
  continuous h->
  (forall eps:R,0<eps->exists N:nat,forall i:nat,(N<=i)%N->
    forall x,K x->mdist (g i x) (f x)<eps)->
  (forall eps:R,0<eps->exists N:nat,forall i:nat,(N<=i)%N->`|eta i|<eps)->
  forall eps:R,0<eps->exists N:nat,forall i:nat,(N<=i)%N->
    forall x,K x->
      `|h (g i x)*(sigma x+eta i)^+m-h (f x)*(sigma x)^+m|<eps.
Proof.
move=>hImage hH hUniform hError.
pose P:=metric_product Y (real_line_metric R).
pose F (x:A):P:=(f x,sigma x).
pose G (i:nat) (x:A):P:=(g i x,sigma x+eta i).
pose H (p:P):R^o:=h p.1 * p.2^+m.
have hSecond:continuous (fun p:P=>(p.2:R^o)).
  exact:(@second_projection_continuous Y (real_line_metric R)).
have hPower:forall k:nat,continuous (fun p:P=>(p.2^+k:R^o)).
  elim=>[|k ih] p.
  - exact:cvg_cst.
  - have hExp:(fun q:P=>q.2^+k.+1)=
      (fun q:P=>q.2*q.2^+k).
      by apply:funext=>q;rewrite exprS.
    rewrite hExp.
    exact:(@cvgM R P (nbhs p) (@nbhs_filter P p)
      (fun q:P=>q.2) (fun q:P=>q.2^+k) p.2 (p.2^+k)
      (hSecond p) (ih p)).
have hHContinuous:continuous H.
  move=>p.
  exact:(@cvgM R P (nbhs p) (@nbhs_filter P p)
    (fun q:P=>h q.1) (fun q:P=>q.2^+m) (h p.1) (p.2^+m)
    (@continuous_comp P Y R^o (fun q:P=>q.1) h p
      (@first_projection_continuous Y (real_line_metric R) p) (hH p.1))
    (hPower m p)).
have hPair:forall eps:R,0<eps->exists N:nat,forall i:nat,(N<=i)%N->
    forall x,K x->mdist (G i x) (F x)<eps.
  move=>eps hEps.
  have[N hN]:=hUniform eps hEps.
  have[M hM]:=hError eps hEps.
  exists (maxn N M)=>i hi x hx.
  have hFirst:=hN i (leq_trans (leq_maxl N M) hi) x hx.
  have hErrorValue:=hM i (leq_trans (leq_maxr N M) hi).
  rewrite /G /F metric_product_distanceE real_line_metric_distanceE /=
    addrAC subrr add0r gt_max.
  by apply/andP;split.
have hResult:=@metric_compact_uniform_composition R A P (real_line_metric R)
  K F G H hImage hHContinuous hPair.
move=>eps hEps.
have[N hN]:=hResult eps hEps.
exists N=>i hi x hx.
have hValue:=hN i hi x hx.
change (is_true (`|h (g i x)*(sigma x+eta i)^+m-
  h (f x)*(sigma x)^+m|<eps)) in hValue.
exact:hValue.
Qed.
