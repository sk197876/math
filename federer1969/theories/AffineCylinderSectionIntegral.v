(** Supporting the integral-geometric assertion in Federer (1969), 2.10.46,
    p. 204. Freilich (1950), Theorem 4.5, Part 4, pp. 245–247, first
    evaluates the scalar integral when the transverse fibre is finite.
    Combine the exact affine fibre bijection with the integral of the finite
    family of equal-length scalar sections. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionBasic
  MeasureIntegralUP CountingMeasure MappingMultiplicity TopologicalBorel LebesgueScalarMeasure
  AffineCylinderFibreCount AffineCylinderFiniteIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [affine_cylinder_finite_fibre_integral]: supporting
    finite-fibre case in 2.10.46, p. 204; Freilich
    (1950), Theorem 4.5, Part 4, pp. 245–247.
    The scalar integral of the actual map's multiplicity is
    the transverse multiplicity times the affine section length.
    Finiteness is required only of this individual transverse
    fibre, not of the whole set V. *)
Theorem affine_cylinder_finite_fibre_integral (R : realType) (X Y : choiceType)
    (f : R*X -> R*Y) (q : X -> Y) (a ell : R) (b : X -> R)
    (T : set (real_line_metric R)) (V : set X) (y : Y) :
  a!=0%R -> (forall t x, f (t,x)=((a*t+b x)%R,q x)) ->
  borel_set T -> lebesgue_scalar_measure T=ell%:E -> finite_set (mapping_fibre q V y) ->
  is_measure_integral (@lebesgue_scalar_measure R) (partial_function_total
    (fun w=>(@mapping_multiplicity R [the choiceType of (R*X)%type] (R*Y)%type
      f (T `*` V) (w,y) : extended_real_line R)))
    ((`|a|*ell)%R%:E*@mapping_multiplicity R X Y q V y).
Proof.
move=> ha hf hT hell hfinite.
have [F hF] := (@finite_fsetP X (mapping_fibre q V y)).1 hfinite.
have hmem x : x \in F <-> V x /\ q x=y.
  change ([set` F] x <-> mapping_fibre q V y x); by rewrite -hF.
have he w : [set j | j \in F /\ T ((w-b j)/a)%R]=
    [set x | V x /\ q x=y /\ T ((w-b x)/a)%R].
  apply/seteqP; split=> x.
  - move=> [hx ht]; have [hv hq] := (hmem x).1 hx; by split=> //; split.
  - move=> [hv [hq ht]]; split=> //; apply/(hmem x); by split.
have hi := @finite_affine_cylinder_section_integral R X F T a ell b ha hT hell.
have hfunc : (fun w=>(counting_measure (R:=R) [set j | j \in F /\ T ((w-b j)/a)%R] : extended_real_line R))=
    (fun w=>(@mapping_multiplicity R [the choiceType of (R*X)%type] (R*Y)%type f (T `*` V) (w,y) : extended_real_line R)).
  apply: funext=> w; rewrite he; exact: esym (@affine_cylinder_fibre_count R X Y f q a b T V w y ha hf).
rewrite hfunc in hi; move: hi; by rewrite /mapping_multiplicity hF.
Qed.
