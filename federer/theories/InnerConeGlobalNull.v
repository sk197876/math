(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.11, p. 338:
    a homogeneous polynomial majorant has global dimension
    equal to its dimension at the origin. The
    measure connection expands its global nullity from
    a null neighbourhood, using positive dilations and
    the existing countable-union law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals
  constructive_ereal topology lra ring.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  InnerProductUP Hom InnerNorm InnerMetric HilbertFormCompactness
  SetGermUP SetGermExistence InnerHausdorffDilation HausdorffMeasure
  MeasureUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Cone.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Local Notation NX:=(inner_norm hB).
Variable hNX:is_real_norm NX.
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation E:=(inner_metric_space hB).

(** Source for [inner_cone_global_null_from_germ]: the
    global homogeneous majorant in 3.4.11, p. 338.
    Positive dilation invariance turns any null representative
    of its origin germ into a global null set.
    Every natural Hausdorff degree and zero vector remain. *)
Theorem inner_cone_global_null_from_germ (S A:set X) k:
  (forall t:R,0<t ->forall x,S x ->S (t*:x)) ->
  @set_germ T 0 A=@set_germ T 0 S ->
  @hausdorff_measure R E k A=0%E ->@hausdorff_measure R E k S=0%E.
Proof.
move=>hCone hGerm hNull.
have [U [hU [hU0 hEqual]]]:=(@set_germ_equality_original T 0 A S).1 hGerm.
have hInterior:norm_domain_interior NX U 0.
  rewrite openE in hU.
  exact:((@norm_domain_interior_neighbourhood R X NX hNX U 0).2 (hU 0 hU0)).
have [r [hr hBall]]:=hInterior.
pose C:set X:=S `&` [set x|NX x<r].
have hCA:C `<=` A.
  move=>x [hx hxSmall].
  have hUx:=hBall x hxSmall;rewrite add0r in hUx.
  have h:(S `&` U) x by split.
  by rewrite -hEqual in h;exact:h.1.
have hCNull:@hausdorff_measure R E k C=0%E.
  exact:(@measure_null_subset R E (@hausdorff_measure R E k) (@hausdorff_measure_is_measure R E k) C A hCA hNull).
pose F:=fun j:nat=>(fun x:X=>(j.+1)%:R*:x) @` C.
have hEach j:@hausdorff_measure R E k (F j)=0%E.
  rewrite /F (@inner_hausdorff_positive_dilation R X B hB k (j.+1)%:R C).
  - by rewrite hCNull mule0.
  - by rewrite ltr0n.
have hCover:S `<=` \bigcup_(j in (@setT nat)) F j.
  move=>x hx.
  pose a:=NX x/r.
  have ha:0<=a:=divr_ge0 (real_seminorm_nonnegative hNX.1 x) (ltW hr).
  pose j:=Num.bound a.
  have hLarge:a<j%:R:=archi_boundP ha.
  have hPositive:(0:R)<(j.+1)%:R by rewrite ltr0n.
  have hInv:0<((j.+1)%:R:R)^-1 by rewrite invr_gt0.
  have hBigger:a<(j.+1)%:R.
    apply:lt_le_trans hLarge _;by rewrite ler_nat leqnSn.
  exists j;first done.
  exists (((j.+1)%:R)^-1*:x);last by rewrite scalerA mulfV ?gt_eqF // scale1r.
  split;first exact:hCone _ hInv x hx.
  change (is_true (NX (((j.+1)%:R)^-1*:x)<r)).
  rewrite (real_seminorm_scale hNX.1) (ger0_norm (ltW hInv)).
  have hNr:NX x<(j.+1)%:R*r.
    move:hBigger;by rewrite /a ltr_pdivrMr //.
  rewrite mulrC ltr_pdivrMr //;by rewrite mulrC.
have hUnion:=@measure_null_countable_union R E (Choice.clone nat _)
  (@hausdorff_measure R E k) (@hausdorff_measure_is_measure R E k) setT F
  (countableP setT) (fun j _=>hEach j).
exact:(@measure_null_subset R E (@hausdorff_measure R E k) (@hausdorff_measure_is_measure R E k) S _ hCover hUnion).
Qed.
End Cone.
