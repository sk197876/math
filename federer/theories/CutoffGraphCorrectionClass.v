(** Federer (1969), 3.1.23, p. 237: the
    cutoff-weighted local graph correction is globally class k. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom TensorUP RealNormUP NormMetric NormDifferentialUP NormRegularity
  NormRegularityOperations NormCutoffProductClass NormOpenDomainLaws ScaledCutoffUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [cutoff_graph_correction_class]: class k and
    exterior identity of f=x+u(x)(p*-psi)[p(x)] in Federer
    3.1.23, p. 237, with the translations retained.
    The local graph representative is used only on its actual
    open domain; the closed cutoff ball lies inside that domain. *)
Lemma cutoff_graph_correction_class (R:realType) (X:lmodType R)
    (N:X->R) (hN:is_real_norm N) (U:set X) b t r (w:X->R^o) C (W F:X->X) k :
  is_scaled_annular_cutoff hN b t r w C ->
  norm_class hN hN U W k ->
  @closed (real_norm_metric_space hN) [set x|N (x-b)<=r] ->
  (forall x,N (x-b)<=r -> U x) ->
  (forall x,F x=x+w x*:W x) ->
  norm_class hN hN setT F k /\ forall x,r<=N (x-b) -> F x=x.
Proof.
move=>hw hW hP hPU hF.
have hz x (hx:~N (x-b)<=r):w x=0.
  apply: (scaled_cutoff_outer hw); apply: ltW.
  rewrite ltNge; apply/negP=>hle; exact (hx hle).
have hp:=@norm_class_cutoff_product R X X N N hN hN U [set x|N (x-b)<=r]
  w W k hW (scaled_cutoff_smooth hw k) hP hPU hz.
pose Id:=hom_of_linear (linear_id X).
have hId:norm_bounded_linear N N Id.
  exists 1; split; first exact: ler01.
  by move=>v; rewrite /Id hom_of_linearE /= mul1r.
have hi:=@norm_class_linear R X X N N hN hN setT Id k
  (fun x _=>norm_full_domain_interior N x) hId.
split.
- exact (norm_class_domain_agreement (fun x _=>esym (hF x)) (norm_class_add hi hp)).
- move=>x hx; by rewrite hF (scaled_cutoff_outer hw hx) scale0r addr0.
Qed.
