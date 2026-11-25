(** Federer (1969), 3.3.3, p. 288: a lies in the closure
    of the original punctured affine fibre. Keep the actual
    kernel plane and use every positive neighbourhood through
    cofinal reciprocal metric radii. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets functions reals topology.
From Federer Require Import GrassmannSubspaces ModuleQuotient EuclideanInnerProduct InnerMetric InnerNorm
  EuclideanProjectionSpace StructureProjectionKernel ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_fibre_accumulation]: the set
    displayed in Federer 3.3.3, p. 288, paraphrased:
    the centre belongs to the closure of points of A other
    than itself whose displacement lies in the original ker p. *)
Definition structure_fibre_accumulation (R:realType) n m (hmn:(m<=n)%N)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (z:inner_metric_space (@euclidean_inner_productP R n)*
      euclidean_projection_space R n m):Prop:=
  closure [set x:inner_metric_space (@euclidean_inner_productP R n)|
    A x /\ x!=z.1 /\ grassmann_val (structure_projection_kernel hmn z.2) (x-z.1)] z.1.

(** Source for [structure_fibre_accumulation_equations]: the
    equality-of-projections description in the proof of
    Federer 3.3.3, p. 288. It is exactly membership
    in the original affine kernel fibre, without a supplied
    distance or kernel equation premise. *)
Lemma structure_fibre_accumulation_equations (R:realType) n m (hmn:(m<=n)%N)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (z:inner_metric_space (@euclidean_inner_productP R n)*euclidean_projection_space R n m):
  structure_fibre_accumulation hmn A z <->
  closure [set x:inner_metric_space (@euclidean_inner_productP R n)|
    A x /\ x!=z.1 /\ euclidean_projection_linear z.2 x=euclidean_projection_linear z.2 z.1] z.1.
Proof.
have he:[set x:inner_metric_space (@euclidean_inner_productP R n)|
    A x /\ x!=z.1 /\ grassmann_val (structure_projection_kernel hmn z.2) (x-z.1)]=
    [set x:inner_metric_space (@euclidean_inner_productP R n)|
    A x /\ x!=z.1 /\ euclidean_projection_linear z.2 x=euclidean_projection_linear z.2 z.1].
  apply/seteqP; split=>x [hA [hNe hFibre]]; split=>//; split=>//.
  - have hZero:euclidean_projection_linear z.2 (x-z.1)=0:=
      (structure_projection_kernelE hmn z.2 (x-z.1)).1 hFibre.
    by move/eqP:hZero; rewrite linearB subr_eq0=>/eqP.
  - apply/(structure_projection_kernelE hmn z.2 (x-z.1)).
    by rewrite linearB hFibre subrr.
by rewrite /structure_fibre_accumulation he.
Qed.

(** Source for [structure_fibre_accumulation_reciprocals]: the
    countable neighbourhood characterization used in Federer
    3.3.3, p. 288. Positive reciprocal natural radii
    are cofinal among all positive real radii; points remain
    in the original A and original punctured affine fibre. *)
Theorem structure_fibre_accumulation_reciprocals (R:realType) n m (hmn:(m<=n)%N)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (z:inner_metric_space (@euclidean_inner_productP R n)*euclidean_projection_space R n m):
  structure_fibre_accumulation hmn A z <->forall i,
  exists x:inner_metric_space (@euclidean_inner_productP R n),
    A x /\ euclidean_projection_linear z.2 x=euclidean_projection_linear z.2 z.1 /\
    0<inner_norm (@euclidean_inner_productP R n) (x-z.1)<((i.+1)%:R:R)^-1.
Proof.
rewrite structure_fibre_accumulation_equations; split.
- move=>hClosure i.
  have hPos:0<((i.+1)%:R:R)^-1 by rewrite invr_gt0 ltr0n.
  have hn:nbhs z.1 [set x|mdist z.1 x<((i.+1)%:R:R)^-1].
    apply:(proj2 (metricType_numDomainType.nbhs_mdistP z.1 _)).
    by exists ((i.+1)%:R:R)^-1.
  have [x [[hA [hNe hEq]] hNear]]:=hClosure _ hn.
  exists x; split=>//; split=>//; apply/andP; split.
  + by rewrite inner_norm_gt0 subr_eq0.
  + change (is_true (mdist z.1 x<((i.+1)%:R:R)^-1)) in hNear.
    by move:hNear; rewrite inner_metric_distanceE -[z.1-x]opprB inner_normN.
- move=>hNear U hU.
  have [e he hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP z.1 U) hU.
  have [i hSmall]:=positive_reciprocal_nat_small he.
  have [x [hA [hEq /andP [hPos hDist]]]]:=hNear i.
  exists x; split.
  + split=>//; split=>//.
    by move:hPos; rewrite inner_norm_gt0 subr_eq0.
  + apply:hBall; change (is_true (mdist z.1 x<e)).
    rewrite inner_metric_distanceE -[z.1-x]opprB inner_normN.
    exact:(lt_trans hDist hSmall).
Qed.
