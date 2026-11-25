(** Federer (1969), 3.2.28(1), printed p. 263:
    the smooth regular-level straightening obtained from
    3.1.18–3.1.19. The translation, source chart and
    all inverses are fixed at every derivative order. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations
  GrassmannSubspaces EuclideanInnerProduct InnerNorm HilbertFormCompactness
  NormDifferentialUP NormRegularity NormDiffeomorphismUP
  NormDiffeomorphismComposition NormDiffeomorphismSourceRestriction
  NormTranslationDiffeomorphism ConstantRankChartUP EuclideanBlockLinearMaps
  EuclideanProductBox EuclideanCoordinatePlane EuclideanSubmanifoldUP
  FiniteInnerSmoothSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [constant_rank_smooth_fibre_straightening]: the
    fixed smooth chart for a level set, supporting
    Federer 3.2.28(1), p. 263, by 3.1.19(2),
    p. 231. This is the printed affine coordinate
    fibre translated to a vector plane, with no chart
    choices depending on the derivative order. *)
Theorem constant_rank_smooth_fibre_straightening (R:realType) v l n
    (f:R_n R (v+l)->R_n R n)
    (D:R_n R (v+l)->Hom (R_n R (v+l)) (R_n R n)) b U e p j g G psi:
  (forall k,@is_euclidean_constant_rank_chart R v l n k
    (fun _=>True) f D b U e p j g G psi) ->
  exists (C:set (R_n R (v+l))) (s t:R_n R (v+l)->R_n R (v+l))
    (Z:GrassmannSubspaces.G (R_n R (v+l)) l),forall k,
    is_submanifold_straightening k [set x|f x=f b] b U C s t Z.
Proof.
move=>hC.
pose X:=R_n R (v+l).
pose NX:=inner_norm (@euclidean_inner_productP R (v+l)).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R (v+l)).
pose P:=@euclidean_product_box R v l (g b) e.
pose rb:=@euclidean_first_block_map R v l.
pose Ib:=@euclidean_first_injection_map R v l.
pose c:=Ib (rb (g b)).
pose C:=fun y:X=>True /\ P (y+c).
pose s:=fun x:X=>g x-c.
pose t:=fun y:X=>G (y+c).
have [Z hZ]:=@euclidean_last_coordinate_plane R v l.
have hUa:U b:=constant_rank_base_member (hC 1%N).
have hComp k:is_norm_diffeomorphism hNX hNX U C s t k.
  have htr:=@norm_translation_diffeomorphism R X NX hNX c k.
  have hOpen x (hx:P x):norm_domain_interior NX P x:=euclidean_product_box_open hx.
  have htrP:=@norm_diffeomorphism_source_restriction R X X NX NX hNX hNX
    (fun _=>True) P (fun _=>True) (fun x=>x-c) (fun y=>y+c) k
    htr (fun x _=>I) hOpen.
  exact:(@norm_diffeomorphism_composition R X X X NX NX NX hNX hNX hNX
    U P C g G (fun x=>x-c) (fun y=>y+c) k
    (constant_rank_source_chart (hC k)) htrP).
have hLocal x (hx:U x):f x=f b <->rb (s x)=0.
  have hpf:f x=f b <->p (f x)=p (f b).
    split; first by move=>->.
    move=>heq; rewrite (constant_rank_section_factor (hC 1%N) hx)
      (constant_rank_section_factor (hC 1%N) hUa) heq; reflexivity.
  rewrite hpf -(constant_rank_source_prefix (hC 1%N) hx)
    -(constant_rank_source_prefix (hC 1%N) hUa).
  have hrc:rb c=rb (g b):=@euclidean_first_block_injectionK R v l (rb (g b)).
  change (rb (g x)=rb (g b) <->rb (g x-c)=0).
  rewrite (linB (hom_linear rb)) hrc.
  split; first by move=>->; rewrite subrr.
  move=>heq; apply/eqP; by rewrite -subr_eq0 heq eqxx.
exists C,s,t,Z; move=>k; constructor.
- have hc:=norm_class_continuous
    (norm_diffeomorphism_forward_class (constant_rank_source_chart (hC 1%N))).
  exact:(@hc b hUa).1.
- exact:hComp.
- apply/seteqP; split=>y.
  + move=>[x [hfx hUx] hxy]; split.
    * apply:(hZ y).2; rewrite -hxy; exact:(hLocal x hUx).1 hfx.
    * rewrite -hxy; exact:(@norm_diffeomorphism_maps R X X NX NX hNX hNX
        U C s t k (hComp k) x hUx).
  + move=>[hyZ hyC].
    have htU:=@norm_diffeomorphism_inverse_maps R X X NX NX hNX hNX
      U C s t k (hComp k) y hyC.
    have hst:=@norm_diffeomorphism_right_inverse R X X NX NX hNX hNX
      U C s t k (hComp k) y hyC.
    exists (t y); last exact:hst.
    split; last exact:htU.
    apply:(hLocal _ htU).2; rewrite hst; exact:(hZ y).1 hyZ.
Qed.
