(** Federer (1969), 3.1.19, p. 231: condition (2) implies (1).
    The source normal form of 3.1.18 makes the level set an affine
    coordinate fibre, which a translation sends to a vector plane. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom Bilinear ModuleQuotient GrassmannSubspaces GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormDifferentialUP NormClassOneUP NormRegularity NormRankZero
  NormDiffeomorphismUP NormDiffeomorphismComposition NormDiffeomorphismSourceRestriction
  NormTranslationDiffeomorphism LinearRankUP ConstantRankChartUP ConstantRankTheorem
  EuclideanBlockLinearMaps EuclideanProductBox EuclideanCoordinatePlane
  EuclideanSubmanifoldUP SubmanifoldChartsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [regular_level_charts_submanifold]: implication
    (2) to (1) in Federer 3.1.19, p. 231. Neither surjectivity of
    the original target map nor full target rank is assumed; its
    printed constant rank n-mu is sufficient. *)
Theorem regular_level_charts_submanifold (R:realType) n mu k (B:set (R_n R n)) :
  (1<=k)%N -> @has_regular_level_charts R n mu k B ->
  @is_euclidean_submanifold R n mu k B.
Proof.
move=>hk hB b hb.
have [i [T [f [D [hTb [hmn [hni [hf [hD [hlevel hr]]]]]]]]]]:=hB b hb.
have [r hn]:exists r,n=(r+mu)%N by exists (n-mu)%N; rewrite subnK.
subst n.
rewrite addnK in hr hni.
pose X:=R_n R (r+mu).
pose NX:=inner_norm (@euclidean_inner_productP R (r+mu)).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R (r+mu)).
have hgen:norm_generic_rank NX T D b r.
  have [d [hd hball]]:=hTb.
  exists d; split=>// h hh; split; first exact: hball.
  exact: hr (hball h hh).
have [U [e [p [j [g [G [psi hC]]]]]]]:=@federer_3_1_18 R r mu i T f D b k hk hf hD hgen.
pose P:=@euclidean_product_box R r mu (g b) e.
pose rb:=@euclidean_first_block_map R r mu.
pose Ib:=@euclidean_first_injection_map R r mu.
pose c:=Ib (rb (g b)).
have hchart:=constant_rank_source_chart hC.
have htr:=@norm_translation_diffeomorphism R X NX hNX c k.
have hopenP x (hx:P x):norm_domain_interior NX P x:=euclidean_product_box_open hx.
have htrP:=@norm_diffeomorphism_source_restriction R X X NX NX hNX hNX
  (fun _=>True) P (fun _=>True) (fun x=>x-c) (fun y=>y+c) k htr (fun _ _=>I) hopenP.
have hcomp:=@norm_diffeomorphism_composition R X X X NX NX NX hNX hNX hNX
  U P (fun y=>True /\ P (y+c)) g G (fun x=>x-c) (fun y=>y+c) k hchart htrP.
pose C:=fun y:X=>True /\ P (y+c).
pose s:=fun x:X=>g x-c.
pose t:=fun y:X=>G (y+c).
have [Z hZ]:=@euclidean_last_coordinate_plane R r mu.
have hUa:U b:=constant_rank_base_member hC.
have hUT:=constant_rank_domain_subset hC.
have hlocal x (hx:U x):B x <-> rb (s x)=0.
  have hxT:=hUT x hx.
  have hBx:B x <-> f x=f b.
    split.
    - move=>hBx; have hh:(B `&` T) x:=conj hBx hxT; rewrite hlevel in hh; exact hh.2.
    - move=>heq; have hh:(B `&` T) x by rewrite hlevel; split.
      exact hh.1.
  have hpf: f x=f b <-> p (f x)=p (f b).
    split; first by move=>->.
    move=>heq; rewrite (constant_rank_section_factor hC hx)
      (constant_rank_section_factor hC hUa) heq; reflexivity.
  rewrite hBx hpf -(constant_rank_source_prefix hC hx) -(constant_rank_source_prefix hC hUa).
  have hrc:rb c=rb (g b):=@euclidean_first_block_injectionK R r mu (rb (g b)).
  change (rb (g x)=rb (g b) <-> rb (g x-c)=0).
  rewrite (linB (hom_linear rb)) hrc.
  split; [move=>->; exact: subrr|move=>heq; apply/eqP; by rewrite -subr_eq0 heq eqxx].
exists U,C,s,t,Z; constructor.
- have hc:=norm_class_continuous (norm_diffeomorphism_forward_class hchart).
  exact (@hc b hUa).1.
- exact hcomp.
- apply/seteqP; split=>y.
  + move=>[x [hBx hUx] hxy]; split.
    * apply: (hZ y).2; rewrite -hxy; exact: (hlocal x hUx).1 hBx.
    * rewrite -hxy; exact (@norm_diffeomorphism_maps R X X NX NX hNX hNX U C s t k hcomp x hUx).
  + move=>[hyZ hyC].
    have htU:=@norm_diffeomorphism_inverse_maps R X X NX NX hNX hNX U C s t k hcomp y hyC.
    have hst:=@norm_diffeomorphism_right_inverse R X X NX NX hNX hNX U C s t k hcomp y hyC.
    exists (t y); last exact hst.
    split=>//; apply: (hlocal _ htU).2; rewrite hst; exact: (hZ y).1 hyZ.
Qed.
