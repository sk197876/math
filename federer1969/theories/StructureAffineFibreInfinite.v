(** Federer (1969), 3.3.10, p. 296: original punctured
    affine-fibre accumulation forces the ORIGINAL fibre infinite. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals topology.
From Federer Require Import RealMetricBackground GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanProjectionSpace StructureProjectionKernel StructurePlaneGrowth StructureFibreAccumulation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [structure_punctured_fibre_accumulation_infinite]:
    the cluster-point observation in the proof of Federer 3.3.10,
    p. 296. A finite original fibre would have a finite, hence
    closed, punctured subset; its closure cannot contain the removed
    centre. No original source closedness or measurability is needed. *)
Lemma structure_punctured_fibre_accumulation_infinite (R:realType)
    (X:metricType R) (Y:Type) (f:X->Y) (A:set X) (a:X):
  closure [set x:X|A x /\x!=a /\f x=f a] a ->
  ~finite_set (A `&` f @^-1` [set f a]).
Proof.
move=>hAccum hFinite.
pose C:set X:=[set x|A x /\x!=a /\f x=f a].
have hSub:C `<=` (A `&` f @^-1` [set f a]).
  move=>x [hx [_ hEq]]; by split.
have hCFinite:finite_set C:=sub_finite_set hSub hFinite.
have hClosed:closed C.
  have hAccessible:accessible_space X:=hausdorff_accessible (@metric_hausdorff R X).
  have hAll:forall D:set X,finite_set D ->closed D.
    exact ((@accessible_finite_set_closed X).1 hAccessible).
  exact:hAll C hCFinite.
have [_ [hNot _]]:=hClosed a hAccum.
by rewrite eqxx in hNot.
Qed.

(** Source for [structure_accumulation_projection_infinite_fibre]:
    the third fixed-projection assertion of Federer 3.3.10, p. 296.
    The image of the ORIGINAL third section lies in the points with
    infinite ORIGINAL A fibre. The actual kernel/projection equality
    identifies the same punctured affine set before the finite-set
    argument; no selected hull or inverse is introduced. *)
Theorem structure_accumulation_projection_infinite_fibre (R:realType) n m (hmn:(m<=n)%N)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m):
  (euclidean_projection_linear p @`
    [set a:inner_metric_space (@euclidean_inner_productP R n)|
      A a /\structure_plane_accumulation A a (structure_projection_kernel hmn p)]) `<=`
  [set y|~finite_set (A `&` euclidean_projection_linear p @^-1` [set y])].
Proof.
move=>y [a [_ hAccum] <-].
change (structure_fibre_accumulation hmn A (a,p)) in hAccum.
have hFibre:closure [set x:inner_metric_space (@euclidean_inner_productP R n)|
    A x /\x!=a /\euclidean_projection_linear p x=euclidean_projection_linear p a] a:=
  (structure_fibre_accumulation_equations hmn A (a,p)).1 hAccum.
exact:(@structure_punctured_fibre_accumulation_infinite R
  (inner_metric_space (@euclidean_inner_productP R n)) (R_n R m)
  (euclidean_projection_linear p) A a hFibre).
Qed.
