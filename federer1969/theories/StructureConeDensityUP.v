(** Federer (1969), 3.3.2, pp. 287–288: the cone-density
    upper limit. State the least-upper-bound laws for the original
    radius/aperture costs and the greatest-lower-bound laws over
    every positive aperture cutoff before proving existence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric
  EuclideanProjectionSpace StructureCone StructureProjectionKernel
  ExtendedRealBoundsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_cone_cost]: the expression
    phi[A intersect X(a,r,ker p,s)] r^(-m) s^(-m) in
    Federer 3.3.2, p. 287. This supporting expression
    retains the original arbitrary A and outer measure. *)
Definition structure_cone_cost (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (z:inner_metric_space (@euclidean_inner_productP R n)*
      euclidean_projection_space R n m) (r s:R): \bar R:=
  (phi (A `&` structure_cone (structure_projection_kernel hmn z.2)
    z.1 r%:E s)*((r^-1)^+m)%:E*((s^-1)^+m)%:E)%E.

(** Source for [is_structure_cone_tail_supremum]: the
    supremum over 0<r<delta and 0<s<t supporting the
    upper limit in Federer 3.3.2, pp. 287–288. The
    independent least-upper-bound specification includes
    infinite values and does not assume a Borel conclusion. *)
Definition is_structure_cone_tail_supremum (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (delta:R) z (t:R) (q: \bar R):Prop:=
  is_extended_real_supremum [set v|exists r s:R,
    (0<r<delta) /\ (0<s<t) /\ v=structure_cone_cost hmn phi A z r s] q.

(** Source for [is_structure_cone_density]: the right-hand
    upper limit of the radius supremum in Federer 3.3.2,
    pp. 287–288, independently specified as the greatest
    lower bound of all positive-cutoff suprema. Existence
    is proved afterwards; no regularity of A is required. *)
Definition is_structure_cone_density (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (delta:R)
    (f:inner_metric_space (@euclidean_inner_productP R n)*
      euclidean_projection_space R n m->\bar R):Prop:=
  forall z,
    (forall t q,0<t ->is_structure_cone_tail_supremum hmn phi A delta z t q ->
      (f z<=q)%E) /\
    (forall b: \bar R,
      (forall t q,0<t ->is_structure_cone_tail_supremum hmn phi A delta z t q ->
        (b<=q)%E) ->(b<=f z)%E).
