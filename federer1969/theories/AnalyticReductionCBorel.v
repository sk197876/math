(** Federer (1969), 3.4.8(5), p. 328:
    the original C_m sets are Borel. Each
    coordinate relation has the proved actual compact
    projection; the original finite intersection
    retains its literal membership equations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology subtype_topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm InnerMetric HomInner LinearGroupTopology
  HilbertFormCompactness LinearBasis OrthogonalGroupTopology AnalyticGermUP AnalyticGermRing
  CommutativeIdealUP AnalyticPrefixGermSubring AnalyticRotatedGermIdeal
  AnalyticRotatedCoordinateRelationBorel TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_reduction_C_borel]: the
    exact original C_m is Borel for every m<n,
    as asserted in 3.4.8(5), p. 328. Each
    original denominator may depend on its coordinate
    index; no common denominator is imposed. *)
Theorem analytic_reduction_C_borel
  (R:realType) (X:lmodType R) (B:X->X->R) (hB:is_inner_product B)
  n (e:'I_n->X) (he:is_basis e) (omega:'I_n->Hom X R^o)
  (hDual:forall i k,omega i (e k)=if i==k then 1 else 0)
  (I:set (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0))
  (gamma:'I_n->@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0)
  (m:'I_n):
  is_commutative_ideal I ->
  borel_set [set g:@orthogonal_group R X B hB n e he|
    forall j:'I_n,(m<=j)%N ->exists delta L,
      @analytic_prefix_germ_subring R X (inner_norm hB) (inner_norm_real_norm hB)
        n e he omega m (ltnW (ltn_ord m)) delta /\
      ~@analytic_rotated_germ_ideal R X B hB n e he I g delta /\
      @analytic_prefix_germ_subring R X (inner_norm hB) (inner_norm_real_norm hB)
        n e he omega (m:nat).+1 (ltn_ord m) L /\
      @analytic_rotated_germ_ideal R X B hB n e he I g (delta*gamma j-L)].
Proof.
move=>hI.
pose NX:=inner_norm hB;pose hNX:=inner_norm_real_norm hB.
pose O:=@orthogonal_group R X B hB n e he.
pose D:set 'I_n:=fun j=>(m<=j)%N.
pose F:=fun j:'I_n=>[set g:O|exists delta L,
  @analytic_prefix_germ_subring R X NX hNX n e he omega m (ltnW (ltn_ord m)) delta /\
  ~@analytic_rotated_germ_ideal R X B hB n e he I g delta /\
  @analytic_prefix_germ_subring R X NX hNX n e he omega (m:nat).+1 (ltn_ord m) L /\
  @analytic_rotated_germ_ideal R X B hB n e he I g (delta*gamma j-L)].
change (borel_set (\bigcap_(j in D) F j)).
apply:(@borel_set_countable_intersection O (Choice.clone 'I_n _) D F).
- exact:(finite_set_countable (@finite_finset (Finite.clone 'I_n _) D)).
- exists m;exact:leqnn.
- move=>j _;exact:(@analytic_rotated_coordinate_relation_borel R X B hB n e he omega hDual
    I m (ltn_ord m) (gamma j) hI).
Qed.
