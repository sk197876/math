(** Endpoint-product estimate for Steiner symmetrisation in Federer (1969),
    2.10.32, pp. 196–197. Choose the four original endpoint families using
    the proved compact-convex section laws, express their differences in
    normal coordinates, and apply the algebraic double-difference norm
    bound. This establishes preservation of an unnormalised top-degree
    endpoint bound before taking the supremum and restoring the cost
    normaliser. The corrected factor in Federer's erratum p. 4, book p. 197
    line 4, is retained in the distinction between endpoint norm and
    normalised cost. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  FiniteCoordinates OrthonormalFamilies UnitNormalGeometry SteinerSymmetrisationUP
  SteinerExteriorEndpointBound NormalEndpointDifferences NormalExteriorNormBound
  ExteriorDiameterUP ExteriorNorm FiniteExteriorPowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [steiner_top_exterior_endpoint_bound]: direct
    endpoint-norm comparison concluding the three
    product expansions of 2.10.32, pp. 196–197.
    Compact convex S is retained; both original
    products have endpoints in S. Degree equals
    the ambient dimension, as required for the
    vanishing hyperplane term. *)
Theorem steiner_top_exterior_endpoint_bound (R : realType) (n : nat)
    (u : R_n R n) (S T : set (inner_metric_space (@euclidean_inner_productP R n))) (M : R) :
  is_steiner_symmetrisation (@euclidean_inner_productP R n) u S T -> compact S -> is_inner_convex S ->
  (forall a b : 'I_n -> R_n R n, (forall i, S (a i)) -> (forall i, S (b i)) ->
    exterior_difference_norm a b<=M) ->
  forall x y : 'I_n -> R_n R n, (forall i, T (x i)) -> (forall i, T (y i)) ->
    exterior_difference_norm x y<=M.
Proof.
move=> hs hc hconv hbound x y hx hy.
pose hB := @euclidean_inner_productP R n.
have hu := steiner_unit_normal_law hs.
have [g [d hgd]] := steiner_original_endpoint_choices hs hc hconv hx hy.
pose v i := normal_foot hB u (x i)-normal_foot hB u (y i).
pose a i := inner_coordinate hB u (x i)-inner_coordinate hB u (y i).
pose f i := g i-d i.
pose p i := normal_foot hB u (x i)+g i*:u.
pose q i := normal_foot hB u (y i)+d i*:u.
pose p2 i := normal_foot hB u (x i)+(g i+2*inner_coordinate hB u (x i))*:u.
pose q2 i := normal_foot hB u (y i)+(d i+2*inner_coordinate hB u (y i))*:u.
have hmid : (fun i=>v i+a i*:u)=(fun i=>x i-y i).
  apply: funext=> i; exact (esym (@normal_endpoint_difference R (R_n R n)
    (@euclidean_inner_product R n) hB u (x i) (y i))).
have hfirst : (fun i=>p2 i-q2 i)=(fun i=>v i+(f i+2*a i)*:u).
  apply: funext=> i; exact (@doubled_parallel_endpoint_difference R (R_n R n)
    (normal_foot hB u (x i)) (normal_foot hB u (y i)) u
    (inner_coordinate hB u (x i)) (inner_coordinate hB u (y i)) (g i) (d i)).
have hsecond : (fun i=>p i-q i)=(fun i=>v i+f i*:u).
  apply: funext=> i; exact (@parallel_endpoint_difference R (R_n R n)
    (normal_foot hB u (x i)) (normal_foot hB u (y i)) u (g i) (d i)).
have hv i : inner_coordinate hB u (v i)=0.
  rewrite /v linearB.
  change (inner_coordinate hB u (normal_foot hB u (x i))-
    inner_coordinate hB u (normal_foot hB u (y i))=0).
  have h0x := @normal_coordinate_foot R (R_n R n) (@euclidean_inner_product R n) hB u hu (x i).
  have h0y := @normal_coordinate_foot R (R_n R n) (@euclidean_inner_product R n) hB u hu (y i).
  exact (eq_trans (congr2 (fun a b : R=>a-b) h0x h0y) (subrr (0 : R))).
have hp := hbound p2 q2 (fun i=>(hgd i).2.1) (fun i=>(hgd i).2.2.2).
have hq := hbound p q (fun i=>(hgd i).1) (fun i=>(hgd i).2.2.1).
rewrite /exterior_difference_norm /exterior_difference_product hfirst in hp.
rewrite /exterior_difference_norm /exterior_difference_product hsecond in hq.
rewrite /exterior_difference_norm /exterior_difference_product -hmid.
exact (@normal_exterior_parallel_shift_norm_bound R (R_n R n) (@euclidean_inner_product R n)
  hB n (@coordinate_basis R n) v a f u M (@coordinate_basisP R n) hu hv hp hq).
Qed.
