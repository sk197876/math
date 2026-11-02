(** Federer (1969), 2.6.6, p. 120: L is the directed union of the
    finite-coordinate spaces L_a. Here a cylinder is specified by its
    coordinate dependence, independently of an enumeration of a. Its
    equivalence with pullbacks is proved separately. Source context:
    CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP CompactSupportFunctionLattice CompactUniformNorm
  VectorFunctionLattice FunctionLatticeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope fset_scope.

Section Cylinders.
Variables (R : realType) (I : choiceType) (Y : I -> topologicalType).
Local Notation X := (prod_topology Y).

(** Source for [is_coordinate_determined]: supporting coordinate
    dependence for L_a in Federer 2.6.6, p. 120. *)
Definition is_coordinate_determined (F : {fset I}) (f : X -> R) :=
  forall x y, (forall i, i \in F -> x i=y i) -> f x=f y.

(** Source for [coordinate_determined_enlarge]: inclusion L_a in L_b
    for a contained in b, Federer 2.6.6, p. 120. *)
Lemma coordinate_determined_enlarge (F G : {fset I}) (f : X -> R) :
  {subset F <= G} -> is_coordinate_determined F f -> is_coordinate_determined G f.
Proof. by move=> hFG hf x y hxy; apply: hf=> i hi; apply: hxy; exact: hFG. Qed.

(** Source for [coordinate_determined_unary]: supporting closure under
    unary pointwise operations in the union L, Federer 2.6.6, p. 120. *)
Lemma coordinate_determined_unary (F : {fset I}) (f : X -> R) (u : R -> R) :
  is_coordinate_determined F f -> is_coordinate_determined F (fun x=>u (f x)).
Proof. by move=> hf x y hxy; rewrite (hf x y hxy). Qed.

(** Source for [coordinate_determined_binary]: supporting common finite
    coordinates for sums and lattice operations, Federer 2.6.6, p. 120. *)
Lemma coordinate_determined_binary (F G : {fset I}) (f g : X -> R) (u : R -> R -> R) :
  is_coordinate_determined F f -> is_coordinate_determined G g ->
  is_coordinate_determined (F `|` G) (fun x=>u (f x) (g x)).
Proof.
move=> hf hg x y hxy; have hF : forall i, i \in F -> x i=y i.
  by move=> i hi; apply: hxy; rewrite in_fsetU hi.
have hG : forall i, i \in G -> x i=y i.
  by move=> i hi; apply: hxy; rewrite in_fsetU hi orbT.
by rewrite (hf x y hF) (hg x y hG).
Qed.

(** Source for [continuous_product_cylinders]: coordinate-dependence
    form of the union L in Federer 2.6.6, p. 120. *)
Definition continuous_product_cylinders : set (X -> R) :=
  [set f | compactly_supported_continuous_functions f /\ exists F, is_coordinate_determined F f].

(** Source for [continuous_product_cylinders_vector_lattice]: the union
    L in Federer 2.6.6, p. 120, is a vector lattice. The closure
    proof uses unions of finite coordinate sets. *)
Theorem continuous_product_cylinders_vector_lattice :
  is_vector_function_lattice continuous_product_cylinders.
Proof.
have hK := @compact_support_vector_lattice R X.
have hscale c f : continuous_product_cylinders f -> continuous_product_cylinders (fun x=>c*f x).
  move=> [hf [F hF]]; split; first exact: hK.2.2 c f hf.
  exists F; exact: (@coordinate_determined_unary F f (fun z=>c*z) hF).
split.
- constructor.
  + move=> f g [hf [F hF]] [hg [G hG]]; split; first exact: (@function_lattice_add R X _ hK.1 f g hf hg).
    exists (F `|` G); exact: coordinate_determined_binary hF hG.
  + by move=> c f hc; exact: hscale.
  + move=> f g [hf [F hF]] [hg [G hG]]; split; first exact: (@function_lattice_minimum R X _ hK.1 f g hf hg).
    exists (F `|` G); exact: coordinate_determined_binary hF hG.
  + move=> c f hc [hf [F hF]]; split; first exact: (@function_lattice_truncation R X _ hK.1 c f hc hf).
    exists F; exact: (@coordinate_determined_unary F f (fun z=>Order.min z c) hF).
  + move=> f g [hf [F hF]] [hg [G hG]] hfg; split; first exact: (@function_lattice_ordered_difference R X _ hK.1 f g hf hg hfg).
    exists (G `|` F); exact: (@coordinate_determined_binary G F g f (fun a b=>a-b) hG hF).
- split; last exact: hscale.
  split; first exact: hK.2.1.
  by exists fset0.
Qed.
End Cylinders.
