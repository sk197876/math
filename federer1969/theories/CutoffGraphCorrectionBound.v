(** Federer (1969), 3.1.23, p. 237: the
    quantitative derivative estimate for the supported graph correction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra ring.
From Federer Require Import Hom TensorUP RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  NormDifferentialLinear NormDifferentialLocal NormDifferentialEnlarge NormDifferentialDirectional
  NormDifferentialArithmetic NormDifferentialScalarProduct NormRegularity NormClassOneUP
  NormOpenDomainLaws ScaledCutoffUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [cutoff_graph_correction_differential_bound]: the
    estimate ||Df-id||<=(C+1)epsilon in Federer 3.1.23,
    p. 237. The product rule gives Du times W
    plus u times DW. On the closed cutoff ball the
    factors are bounded by C/r, epsilon r, 1 and
    epsilon; outside it f is locally identity. *)
Theorem cutoff_graph_correction_differential_bound (R:realType) (X:lmodType R)
    (N:X->R) (hN:is_real_norm N) (U:set X) b t r (w:X->R^o) C (W F:X->X) eps :
  is_scaled_annular_cutoff hN b t r w C -> 0<r -> 0<=C -> 0<=eps ->
  @closed (real_norm_metric_space hN) [set x|N (x-b)<=r] ->
  (forall x,N (x-b)<=r ->
    N (W x)<=eps*N (x-b) /\ exists M:Hom X X,
      has_norm_differential N N U W x M /\ forall v,N (M v)<=eps*N v) ->
  (forall x,F x=x+w x*:W x) ->
  forall x (L:Hom X X),has_norm_differential N N setT F x L ->
    forall v,N (L v-v)<=(eps*(C+1))*N v.
Proof.
move=>hw hr hC heps hP hW hF x L hL v.
pose A:=fun s:R^o=>`|s|.
pose hA:=scalar_absolute_value_norm R.
pose Id:=hom_of_linear (linear_id X).
have hId:norm_bounded_linear N N Id.
  exists 1; split; first exact: ler01.
  by move=>z; rewrite /Id hom_of_linearE /= mul1r.
case:(pselect (N (x-b)<=r))=>[hx|hx].
- have [hmass [M [hM hMb]]]:=hW x hx.
  have [D hD]:=(norm_class_firstP hN hA setT w).1 (scaled_cutoff_smooth hw 1%N).
  have hd:=@norm_class_one_differential R X R^o N A setT w D hD x Logic.I.
  have hdr:=@norm_differential_restrict R X R^o N A setT U w x (D x)
    (fun _ _=>Logic.I) (norm_differential_interior hM) hd.
  have hprod:=norm_differential_scalar_product hN hN hdr hM.
  have hid:=@norm_differential_linear R X X N N hN hN U x Id
    (norm_differential_interior hM) hId.
  have hsum:=norm_differential_add hN hid hprod.
  have hcalc:=norm_differential_domain_agreement hN (fun z _=>esym (hF z)) hsum.
  have hfull:=@norm_differential_enlarge R X X N N U setT F x
    (Id+scalar_vector_product_linear_term (w x) (W x) (D x) M)
    (fun _ _=>Logic.I) hcalc.
  have heq:=norm_differential_unique hN hN hL hfull.
  rewrite heq.
  change (is_true (N ((v+((D x v)*:W x+w x*:M v))-v)<=(eps*(C+1))*N v)).
  rewrite [v+((D x v)*:W x+w x*:M v)]addrC addrK.
  have hu:=scaled_cutoff_differential_bound hw hd v.
  have hwrange:=andP (scaled_cutoff_range hw x).
  have hwr:N (W x)<=eps*r.
    exact (le_trans hmass (ler_wpM2l heps hx)).
  have hNr:0<=N v:=real_seminorm_nonnegative hN.1 v.
  have hNV:0<=N (W x):=real_seminorm_nonnegative hN.1 (W x).
  have hCr:0<=C/r by rewrite divr_ge0 //; exact: ltW hr.
  have hfirst:N ((D x v)*:W x)<=C*eps*N v.
    rewrite (real_seminorm_scale hN.1).
    apply: le_trans (ler_wpM2r hNV hu) _.
    have hh:=ler_wpM2l (mulr_ge0 hCr hNr) hwr.
    apply: le_trans hh _.
    have heq0:(C/r*N v)*(eps*r)=C*eps*N v.
      field; exact: lt0r_neq0 hr.
    by rewrite heq0.
  have hsecond:N (w x*:M v)<=eps*N v.
    rewrite (real_seminorm_scale hN.1) (ger0_norm hwrange.1).
    apply: le_trans (ler_wpM2l hwrange.1 (hMb v)) _.
    have hh:=ler_wpM2r (mulr_ge0 heps hNr) hwrange.2.
    by rewrite mul1r in hh.
  apply: le_trans (real_seminorm_triangle hN.1 _ _) _.
  have hh:=lerD hfirst hsecond.
  have heq0:C*eps*N v+eps*N v=(eps*(C+1))*N v by ring.
  by rewrite heq0 in hh.
- pose O:=fun z=>~N (z-b)<=r.
  have ho:@open (real_norm_metric_space hN) O:=closed_openC hP.
  have hxO:O x:=hx.
  have hOint:norm_domain_interior N O x.
    exact ((@norm_domain_interior_neighbourhood R X N hN O x).2
      (open_nbhs_nbhs (conj ho hxO))).
  have hid:=@norm_differential_linear R X X N N hN hN O x Id hOint hId.
  have hfix z (hz:O z):Id z=F z.
    have hzr:r<=N (z-b).
      apply: ltW; rewrite ltNge; apply/negP=>hle; exact (hz hle).
    by rewrite hF (scaled_cutoff_outer hw hzr) scale0r addr0.
  have hd:=norm_differential_domain_agreement hN hfix hid.
  have hfull:=@norm_differential_enlarge R X X N N O setT F x Id
    (fun _ _=>Logic.I) hd.
  have heq:=norm_differential_unique hN hN hL hfull.
  rewrite heq /Id hom_of_linearE /= subrr (real_seminorm_zero hN.1).
  have hCp:0<=C+1 by lra.
  exact (mulr_ge0 (mulr_ge0 heps hCp) (real_seminorm_nonnegative hN.1 v)).
Qed.
