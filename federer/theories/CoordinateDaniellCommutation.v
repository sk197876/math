(** Federer (1969), 2.6.6, p. 120: order independence of the coordinate
    integrations used to construct finite marginals. This is derived from
    the already proved binary Daniell product, as required by the reference
    to 2.6.4. Source context: CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp mathcomp_extra classical_sets reals topology.
From Federer Require Import RealMetricBackground TopologicalProductMaps ProductCoordinateReplacement
  CoordinateDaniellOperator CompactDaniellIterationCommutation CompactSupportFunctionUP DaniellIntegralUP
  SubtypeCompactHausdorff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [two_coordinate_replacement_continuous]: supporting
    continuity of a two-coordinate section in the finite-product
    argument of Federer 2.6.6, p. 120. *)
Lemma two_coordinate_replacement_continuous (I : choiceType) (Y : I -> topologicalType)
    (i j : I) (x : prod_topology Y) :
  continuous (fun p : Y i*Y j=>(dfwith (dfwith x i p.1) j p.2 : prod_topology Y)).
Proof.
have hc : continuous (fun p : Y i*Y j=>(p.2,(dfwith x i p.1 : prod_topology Y))).
  apply: topological_pair_continuous; first exact: second_projection_continuous.
  move=> p; exact: continuous_comp (@first_projection_continuous (Y i) (Y j) p)
    (@product_coordinate_section_continuous I Y i x p.1).
move=> p; exact: continuous_comp (hc p) (@product_coordinate_replace_continuous I Y j _).
Qed.

(** Source for [coordinate_daniell_operators_commute]: distinct
    factor integrations commute, supporting the consistency of finite
    marginals in Federer 2.6.6, p. 120. *)
Theorem coordinate_daniell_operators_commute (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (A : forall i, (Y i -> R) -> R) (i j : I) :
  i != j -> hausdorff_space (Y i) -> compact (@setT (Y i)) ->
  hausdorff_space (Y j) -> compact (@setT (Y j)) ->
  is_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (A i) ->
  is_daniell_integral (@compactly_supported_continuous_functions R (Y j)) (A j) ->
  forall f, compactly_supported_continuous_functions f ->
    coordinate_daniell_operator A j (coordinate_daniell_operator A i f)=
    coordinate_daniell_operator A i (coordinate_daniell_operator A j f).
Proof.
move=> hij hi hci hj hcj hAi hAj f hf; apply: funext=> x.
pose h := fun p : Y i*Y j=>f (dfwith (dfwith x i p.1) j p.2).
have hh : compactly_supported_continuous_functions h.
  split.
  - move=> p; exact: continuous_comp (@two_coordinate_replacement_continuous I Y i j x p) (hf.1 _).
  - have hc := compact_setX hci hcj.
    have he : (@setT (Y i) `*` @setT (Y j)) = [set: Y i*Y j].
      by apply/seteqP; split=> p hp; [|split].
    rewrite he in hc; exact: subclosed_compact (@real_function_support_closed R _ _) hc (@subsetT _ _).
have he := @compact_daniell_iterations_commute R (Y i) (Y j) (A i) (A j) hi
  (compact_space_locally_compact hci) hj (compact_space_locally_compact hcj) hAi hAj h hh.
rewrite /coordinate_daniell_operator.
have hv : (fun v=>A i (fun u=>f (dfwith (dfwith x j v) i u)))=
    (fun v=>A i (fun u=>h (u,v))).
  apply: funext=> v; congr (A i _); apply: funext=> u.
  by rewrite /h (product_coordinate_replacements_commute u v x hij).
by rewrite hv; exact: he.
Qed.
