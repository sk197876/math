(** Federer (1969), 3.2.35, p. 272:
    the affine-span deficient branch of the
    arbitrary convex-source closure reduction. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerNormedTopology
  EuclideanLinearMaps EuclideanLebesgueDimensions EuclideanLebesgueTranslation EuclideanLebesgueDeterminant
  MeasureUP MeasureBasic MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.


(** Source for [euclidean_singular_affine_fixed_closure_null]:
    supporting the lower-dimensional source case
    in Federer 3.2.35, p. 272. If all
    original differences are fixed by an actual
    singular linear map, so are their closure
    differences by continuity. Its translated range
    is null by the proved determinant transformation
    law. Neither original source measurability nor
    convexity is needed for this support. *)
Theorem euclidean_singular_affine_fixed_closure_null (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:{linear R_n R n->R_n R n}) (a:R_n R n):
  euclidean_det p=0%R ->(forall x,S x ->p (x-a)=x-a) ->
  euclidean_lebesgue_measure n (closure S)=0%E.
Proof.
move=>hDet hFix.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose F:X->X:=fun x=>p (x-a)-(x-a).
pose T:set X:=[set x|p (x-a)=x-a].
have hSubtract:continuous (fun x:X=>(x-a:X)).
  move=>x; apply:(@continuousB R X X (fun z=>z) (fun _=>a) x).
  - exact:cvg_id.
  - exact:cst_continuous.
have hComposite:continuous (fun x:X=>(p (x-a):X)).
  move=>x; exact:(continuous_comp (hSubtract x) (@euclidean_linear_continuous R n p (x-a))).
have hF:continuous F.
  move=>x; exact:(@continuousB R X X (fun z=>p (z-a)) (fun z=>z-a) x
    (hComposite x) (hSubtract x)).
have hT:T=F @^-1` [set (0%R:X)].
  apply/seteqP; split=>x hx.
  - change (p (x-a)-(x-a)=0%R); by rewrite hx subrr.
  - change (p (x-a)-(x-a)=0%R) in hx.
    apply/eqP; by rewrite -subr_eq0 hx.
have hClosed:closed T.
  rewrite hT; apply:preimage_closed; first by move=>x _; exact:hF x.
  exact (@compact_closed [the topologicalType of X] [set (0%R:X)]
    (@metric_hausdorff R [the metricType R of X]) (@compact_set1 [the topologicalType of X] (0%R:X))).
have hSubset:S `<=` T by move=>x hx; exact:hFix x hx.
have hClosureSubset:closure S `<=` T by move=>x hx; exact (hClosed x (@closureS [the topologicalType of X] S T hSubset x hx)).
pose P:set X:=p @` setT.
pose A:set X:=(fun z:X=>a+z) @` P.
have hNull:euclidean_lebesgue_measure n A=0%E.
  by rewrite /A euclidean_lebesgue_translation /P euclidean_lebesgue_linear_image hDet normr0 mul0e.
apply:(@measure_null_subset R X (@euclidean_lebesgue_measure R n)
  (euclidean_lebesgue_is_measure R n) _ A _ hNull)=>x hx.
have hpx:=hClosureSubset x hx.
exists (x-a); last by rewrite addrC subrK.
exists (x-a)=>//; exact hpx.
Qed.
