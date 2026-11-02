(** Federer (1969), 3.1.20, p. 232: the three-piece patched
    map exists and has all the corrected intermediate retraction
    laws. The interpolation formula is checked on its full domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  NormRegularityOperations NormRegularityGluing NormClassZeroTopology NormBoundedLinearTopology
  InnerConvex RetractionUP LocalRetractionUP RetractionPatchUP RetractionPatchBlend
  NormCoordinateTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [retraction_patching_step]: the induction step
    W_(i-1),f_(i-1) to W_i,f_i in Federer 3.1.20, p. 232,
    with the erratum p. 4, book p. 232 lines 11 and 14–15.
    Values land in B and points of B in the actual domain are fixed;
    no unwarranted image inclusion in W_i is imposed. *)
Theorem retraction_patching_step (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (B W T P Q:set X) (V:set Y) (f:X->X) (phi:X->Y) (psi:Y->X) (u:X->R^o) k :
  is_partial_neighbourhood_retraction hNX B W f k ->
  norm_class hNX hNY T phi k -> norm_class hNY hNX V psi k ->
  (forall x,T x -> V (phi x)) -> psi @` V=B `&` T ->
  (forall y,V y -> phi (psi y)=y) -> is_inner_convex V ->
  norm_class hNX (scalar_absolute_value_norm R) (fun _=>True) u k ->
  (forall x,0<=u x<= 1) ->
  @closed [the topologicalType of real_norm_metric_space hNX] P ->
  @open [the topologicalType of real_norm_metric_space hNX] Q ->
  P `<=` T -> Q `<=` P -> (forall x,~P x -> u x=0) -> (forall x,Q x -> u x = 1) ->
  exists h:X->X,
    is_retraction_patch hNX B W T P Q f (fun x=>psi (phi x)) h k /\
    forall x, @retraction_blend_domain R X W T f x ->
      h x= @retraction_blend R X Y f phi psi u x.
Proof.
move=>hpartial hphi hpsi hphiV him hcan hconv hu hrange hP hQ hPT hQP hu0 hu1.
pose A:=W `\` P.
pose D:=@retraction_blend_domain R X W T f.
pose blend:=@retraction_blend R X Y f phi psi u.
pose rho:=fun x=>psi (phi x).
have hblend:=@retraction_blend_class R X Y NX NY hNX hNY B W T V f phi psi u k
  hpartial hphi hpsi hphiV hconv hu hrange.
have hf:=partial_neighbourhood_retraction_class hpartial.
have hAint x (hx:A x):norm_domain_interior NX A x.
  have hW0:=norm_class_continuous hf.
  have hpI:=proj2 (@norm_domain_interior_neighbourhood R X NX hNX (~`P) x)
    (open_nbhs_nbhs (conj (closed_openC hP) hx.2)).
  have [r [hr hW]]:=(@hW0 x hx.1).1.
  have [s [hs hC]]:=hpI.
  exists (Num.min r s); split; first by rewrite lt_min hr hs.
  move=>v; rewrite lt_min=>/andP [hvr hvs]; exact: conj (hW v hvr) (hC v hvs).
have hfA:=@norm_class_open_restriction R X X NX NX hNX hNX W A f k
  (fun x hx=>hx.1) hAint hf.
have hTmap x (hx:T x):T (psi (phi x)).
  have hi:(psi @` V) (psi (phi x)) by exists (phi x)=>//; exact: hphiV.
  by rewrite him in hi; exact hi.2.
have hrho:=@norm_class_compose_on R X Y X NX NY NX hNX hNY hNX T V phi psi k hphiV hphi hpsi.
have hQint x (hx:Q x):norm_domain_interior NX Q x.
  exact (proj2 (@norm_domain_interior_neighbourhood R X NX hNX Q x)
    (open_nbhs_nbhs (conj hQ hx))).
have hrhoQ:=@norm_class_open_restriction R X X NX NX hNX hNX T Q rho k
  (fun x hx=>hPT _ (hQP _ hx)) hQint hrho.
have hagree x (hx:A x) (hd:D x):f x=blend x.
  exact: esym (@retraction_blend_old R X Y NX hNX B W T V f phi psi u k hpartial him hcan x hd (hu0 x hx.2)).
have [g [hg [hgA hgD]]]:=norm_class_compatible_gluing hfA hblend hagree.
have hgQ x (hx:A x \/ D x) (hq:Q x):g x=rho x.
  case:hx=>[ha|hd].
  - by exfalso; exact: ha.2 (hQP x hq).
  - rewrite hgD //; exact (@retraction_blend_new R X Y f phi psi u x (hu1 x hq)).
have [h [hc [hhAD hhQ]]]:=norm_class_compatible_gluing hg hrhoQ hgQ.
have hhA x (hx:A x):h x=f x by rewrite hhAD ?hgA //; by left.
have hhD x (hx:D x):h x=blend x by rewrite hhAD ?hgD //; by right.
have hnew:retraction_patch_domain W T P Q f=(fun x=>(A x \/ D x) \/ Q x) by [].
have hrhoB x (hx:Q x):B (rho x).
  have hi:(psi @` V) (rho x) by exists (phi x)=>//; exact: hphiV (hPT _ (hQP _ hx)).
  by rewrite him in hi; exact hi.1.
have hrhoFixed x (hb:B x) (hq:Q x):rho x=x.
  exact (@retraction_blend_chart_inverse R X Y B T V phi psi him hcan x hb (hPT _ (hQP _ hq))).
exists h; split; last exact hhD.
constructor.
- constructor; first by rewrite hnew; exact hc.
  + move=>x; rewrite hnew.
    move=>[[ha|hd]|hq].
    * rewrite hhA //; exact (@partial_neighbourhood_retraction_range R X NX hNX B W f k hpartial x ha.1).
    * rewrite hhD //; exact (@retraction_blend_range R X Y B W T V f phi psi u hphiV him hconv hrange x hd).1.
    * rewrite hhQ //; exact: hrhoB.
  + move=>x hb; rewrite hnew.
    move=>[[ha|hd]|hq].
    * rewrite hhA //; exact (@partial_neighbourhood_retraction_fixed R X NX hNX B W f k hpartial x hb ha.1).
    * rewrite hhD //; exact (@retraction_blend_fixed R X Y NX hNX B W T V f phi psi u k hpartial him hcan x hb hd).
    * rewrite hhQ //; exact: hrhoFixed.
- move=>x hw hn; exact: hhA (conj hw hn).
- exact hhQ.
- move=>x hn; rewrite hnew; split.
  + move=>[[ha|hd]|hq]; [exact ha.1|exact hd.1|by exfalso; exact: hn (hQP x hq)].
  + move=>hw; left; left; exact: conj hw hn.
- apply/seteqP; split=>x.
  + move=>[hb hx]; split=>//; move: hx; rewrite hnew.
    move=>[[ha|hd]|hq]; [left; exact ha.1|left; exact hd.1|by right].
  + move=>[hb [hw|hq]]; split=>//; rewrite hnew.
    * case:(pselect (P x))=>[hp|hp].
      -- left; right; split=>//; split; first exact: hPT.
         by rewrite (@partial_neighbourhood_retraction_fixed R X NX hNX B W f k hpartial x hb hw); exact: hPT.
      -- left; left; exact: conj hw hp.
    * by right.
Qed.
