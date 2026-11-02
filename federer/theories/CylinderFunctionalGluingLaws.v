(** Federer (1969), 2.6.6, p. 120: linearity and the norm bound of gamma
    follow from the consistent finite marginals. Proofs use only the
    agreement specification, keeping the chosen finite-coordinate
    presentation private. Source context: CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology.
From Federer Require Import FunctionLatticeUP CompactSupportFunctionUP ProductCylinderLattice ConsistentCylinderFunctionalUP
  CompactUniformNorm UniformFunctionNorm UniformFunctionNormUP DaniellSpaceCompactSpace
  FunctionLatticeSeminormUP NormalizedMonotoneUniformBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope fset_scope.

Section Glued.
Variables (R : realType) (I : choiceType) (Y : I -> topologicalType).
Local Notation X := (prod_topology Y).
Variables (A : {fset I} -> (X -> R) -> R) (B : (X -> R) -> R).
Hypothesis hA : is_consistent_cylinder_functional_family A.
Hypothesis hB : is_glued_cylinder_functional A B.

(** Source for [glued_cylinder_functional_linear]: linearity of
    gamma on L, Federer 2.6.6, p. 120. A common finite
    coordinate set handles each pair of summands. *)
Theorem glued_cylinder_functional_linear :
  is_linear_functional_on_functions (@continuous_product_cylinders R I Y) B.
Proof.
have hK := @compact_support_vector_lattice R X.
split.
- move=> f g [hf [F hF]] [hg [G hG]].
  have hFG : {subset F <= F `|` G} by move=> i hi; rewrite in_fsetU hi.
  have hGF : {subset G <= F `|` G} by move=> i hi; rewrite in_fsetU hi orbT.
  have hfH : continuous_coordinate_functions (F `|` G) f.
    split=> //; exact: coordinate_determined_enlarge hFG hF.
  have hgH : continuous_coordinate_functions (F `|` G) g.
    split=> //; exact: coordinate_determined_enlarge hGF hG.
  have hs : continuous_coordinate_functions (F `|` G) (fun x=>(f x+g x)%R).
    split; first exact (@function_lattice_add R X _ hK.1 f g hf hg).
    exact: coordinate_determined_binary hF hG.
  rewrite (@hB _ _ hs) (@hB _ _ hfH) (@hB _ _ hgH).
  exact: (cylinder_family_linear hA (F `|` G)).1 f g hfH hgH.
- move=> c f [hf [F hF]].
  have hs : continuous_coordinate_functions F (fun x=>(c*f x)%R).
    split; first exact: hK.2.2 c f hf.
    exact: coordinate_determined_unary hF.
  rewrite (@hB _ _ hs) (@hB _ _ (conj hf hF)).
  exact: (cylinder_family_linear hA F).2 c f (conj hf hF).
Qed.

(** Source for [glued_cylinder_functional_monotone]: monotonicity
    inherited by gamma from the finite products, Federer 2.6.6,
    p. 120. *)
Lemma glued_cylinder_functional_monotone : forall f g,
  continuous_product_cylinders f -> continuous_product_cylinders g -> function_le f g -> B f<=B g.
Proof.
move=> f g [hf [F hF]] [hg [G hG]] hfg.
have hFG : {subset F <= F `|` G} by move=> i hi; rewrite in_fsetU hi.
have hGF : {subset G <= F `|` G} by move=> i hi; rewrite in_fsetU hi orbT.
have hfH : continuous_coordinate_functions (F `|` G) f.
  split=> //; exact: coordinate_determined_enlarge hFG hF.
have hgH : continuous_coordinate_functions (F `|` G) g.
  split=> //; exact: coordinate_determined_enlarge hGF hG.
rewrite (@hB _ _ hfH) (@hB _ _ hgH).
exact (@cylinder_family_monotone R I Y A hA (F `|` G) f g hfH hgH hfg).
Qed.

(** Source for [glued_cylinder_functional_one]: gamma(1) = 1,
    Federer 2.6.6, p. 120. The empty coordinate set suffices. *)
Lemma glued_cylinder_functional_one : compact (@setT X) -> B (fun _=>1) = 1.
Proof.
move=> hc; have h1 : @continuous_coordinate_functions R I Y fset0 (fun _ : X=>1).
  split; first exact: (@compact_space_constant_one R X hc).
  by move=> x y hxy.
by rewrite (@hB _ _ h1) (cylinder_family_one hA).
Qed.

(** Source for [glued_cylinder_functional_norm_bound]: the displayed
    estimate |gamma|<=nu in Federer 2.6.6, p. 120. *)
Theorem glued_cylinder_functional_norm_bound : compact (@setT X) ->
  forall f, continuous_product_cylinders f -> `|B f|<=compact_support_uniform_norm f.
Proof.
move=> hc.
have h1 : @continuous_product_cylinders R I Y (fun _ : X=>1).
  split; first exact: (@compact_space_constant_one R X hc).
  by exists fset0.
move=> f hf; apply: (@normalized_monotone_functional_uniform_bound R X _ B
  (@continuous_product_cylinders_vector_lattice R I Y) h1 glued_cylinder_functional_linear
  (glued_cylinder_functional_one hc) glued_cylinder_functional_monotone f _ hf).
exact: compact_support_uniform_norm_specification hf.1.
Qed.
End Glued.
