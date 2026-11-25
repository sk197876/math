(** Federer (1969), 3.1.23, p. 237: translate
    and scale the normalized smooth annular cutoff. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP NormDifferentialLinear
  NormDifferentialLocal NormDifferentialDirectional NormDifferentialArithmetic NormDifferentialSubtraction
  NormDifferentialChain NormOpenDomainLaws NormClassOneUP NormRegularity NormRegularityOperations
  AnnularCutoffUP ScaledCutoffUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scaled_annular_cutoff_exists]: the scaled map
    u in Federer 3.1.23, p. 237, including its
    exact plateau and exterior vanishing, global smoothness and
    the derivative bound C/r. Only the normalized cutoff laws
    are used; its construction remains hidden behind its seal. *)
Theorem scaled_annular_cutoff_exists (R:realType) (X:lmodType R)
    (N:X->R) (hN:is_real_norm N) t (u:X->R^o) C b r :
  is_norm_annular_cutoff hN t u C -> 0<r ->
  exists w,is_scaled_annular_cutoff hN b t r w C.
Proof.
move=>hu hr.
pose A:=fun s:R^o=>`|s|.
pose hA:=scalar_absolute_value_norm R.
pose alpha:=fun x=>r^-1*:(x-b).
pose w:=fun x=>u (alpha x).
pose Id:=hom_of_linear (linear_id X).
have hId:norm_bounded_linear N N Id.
  exists 1; split; first exact: ler01.
  by move=>v; rewrite /Id hom_of_linearE /= mul1r.
have hNorm x:N (alpha x)=N (x-b)/r.
  rewrite /alpha (real_seminorm_scale hN.1) ger0_norm; first by rewrite mulrC.
  by rewrite invr_ge0; exact: ltW hr.
have halpha k:norm_class hN hN (fun _=>True) alpha k.
  have hi:=@norm_class_linear R X X N N hN hN (fun _=>True) Id k
    (fun x _=>norm_full_domain_interior N x) hId.
  have hc:=@norm_class_constant R X X N N hN hN (fun _=>True) b k
    (fun x _=>norm_full_domain_interior N x).
  exact (norm_class_scale r^-1 (norm_class_subtract hi hc)).
have hsmooth:norm_class_all_orders hN hA (fun _=>True) w.
  move=>k; exact (norm_class_compose_on (fun _ _=>Logic.I) (halpha k)
    (annular_cutoff_smooth hu k)).
exists w; constructor.
- move=>x; exact (annular_cutoff_range hu (alpha x)).
- move=>x hx; apply: (annular_cutoff_inner hu).
  by rewrite hNorm ler_pdivrMr.
- move=>x hx; apply: (annular_cutoff_outer hu).
  by rewrite hNorm ler_pdivlMr // mul1r.
- exact hsmooth.
- move=>x L hL v.
  have hid:=@norm_differential_linear R X X N N hN hN (fun _=>True) x Id
    (norm_full_domain_interior N x) hId.
  have hcb:=@norm_differential_constant R X X N N hN hN (fun _=>True) x b
    (norm_full_domain_interior N x).
  have hshift:=norm_differential_subtract hN hN hid hcb.
  rewrite subr0 in hshift.
  have had:=norm_differential_scale hN hN r^-1 hshift.
  have [D hD]:=(norm_class_firstP hN hA (fun _=>True) u).1 (annular_cutoff_smooth hu 1%N).
  have hd:=@norm_class_one_differential R X R^o N A (fun _=>True) u D hD (alpha x) Logic.I.
  have hc:=norm_differential_chain hN hN hA had hd.
  have hcr:=@norm_differential_restrict R X R^o N A (fun _=>True /\ True)
    (fun _=>True) w x (hom_comp (D (alpha x)) (r^-1*:Id))
    (fun _ _=>conj Logic.I Logic.I) (norm_full_domain_interior N x) hc.
  have heq:=norm_differential_unique hN hA hL hcr.
  rewrite heq hom_compE hom_scaleE /Id hom_of_linearE /=.
  have hb:=annular_cutoff_differential_bound hu hd (r^-1*:v).
  have hri:0<=r^-1 by rewrite invr_ge0; exact: ltW hr.
  rewrite (real_seminorm_scale hN.1) (ger0_norm hri) in hb.
  apply: le_trans hb _.
  by rewrite mulrA.
Qed.
