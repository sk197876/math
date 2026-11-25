(** Federer (1969), 2.3.8, pp. 78–79: pointwise vector operations on partial
    functions, with their common domains. Erratum p. 1, book p. 78 line 7,
    corrects 'vectorspace' to 'set'; these operations do not assert
    vector-space laws on partial graphs. *)
From mathcomp Require Import all_boot all_algebra classical_sets.
From Federer Require Import PartialFunctionUP PartialFunctionPair PartialFunctionPostcomposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [partial_vector_add]: pointwise sum used in
    Federer 2.3.8, p. 78, on the common domain. *)
Definition partial_vector_add (K : fieldType) (X : Type) (V : lmodType K)
    (f g : partial_function X V) :=
  partial_function_postcompose (partial_function_pair f g) (fun p => p.1+p.2).

(** Source for [partial_vector_subtract]: pointwise difference
    defining the pseudodistance in Federer 2.3.8, p. 78. *)
Definition partial_vector_subtract (K : fieldType) (X : Type) (V : lmodType K)
    (f g : partial_function X V) :=
  partial_function_postcompose (partial_function_pair f g) (fun p => p.1-p.2).

(** Source for [partial_vector_scale]: pointwise scalar product
    used in Federer 2.3.8, p. 79, with unchanged domain. *)
Definition partial_vector_scale (K : fieldType) (X : Type) (V : lmodType K)
    (c : K) (f : partial_function X V) :=
  partial_function_postcompose f (fun y => c *: y).

(** Source for [partial_vector_add_graph]: supporting graph
    evaluation for the sum in Federer 2.3.8, p. 78. *)
Lemma partial_vector_add_graph (K : fieldType) (X : Type) (V : lmodType K)
    (f g : partial_function X V) x z :
  partial_function_graph (partial_vector_add f g) x z <->
  exists a b, partial_function_graph f x a /\ partial_function_graph g x b /\ z=a+b.
Proof.
split.
- move=> [[a b] [[ha hb] hz]]; exists a,b; by split=> //; split.
- move=> [a [b [ha [hb hz]]]]; exists (a,b); by split=> //; split.
Qed.

(** Source for [partial_vector_subtract_graph]: supporting graph
    evaluation for the difference in Federer 2.3.8, p. 78. *)
Lemma partial_vector_subtract_graph (K : fieldType) (X : Type) (V : lmodType K)
    (f g : partial_function X V) x z :
  partial_function_graph (partial_vector_subtract f g) x z <->
  exists a b, partial_function_graph f x a /\ partial_function_graph g x b /\ z=a-b.
Proof.
split.
- move=> [[a b] [[ha hb] hz]]; exists a,b; by split=> //; split.
- move=> [a [b [ha [hb hz]]]]; exists (a,b); by split=> //; split.
Qed.

(** Source for [partial_vector_scale_graph]: supporting graph
    evaluation for scalar multiplication in Federer 2.3.8, p. 79. *)
Lemma partial_vector_scale_graph (K : fieldType) (X : Type) (V : lmodType K)
    (c : K) (f : partial_function X V) x z :
  partial_function_graph (partial_vector_scale c f) x z <->
  exists a, partial_function_graph f x a /\ z=c *: a.
Proof. split; move=> [a [ha hz]]; exists a; split=> //; by symmetry. Qed.
