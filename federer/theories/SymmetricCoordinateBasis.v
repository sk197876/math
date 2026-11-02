(** Federer (1969), 1.9.2, p. 42: the monomial basis is proved by induction
    on the dimension, using the direct-sum isomorphism. This supporting
    construction first gives the recursively indexed homogeneous basis.
    Arbitrary fields and the zero-dimensional case are included. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg finmap.
From Federer Require Import GradedBasis Graded LinearBasis TensorBasis FiniteCoordinates
  SymmetricAlgebra SymmetricGrading SymmetricMaps SymmetricDirectSum
  SymmetricMultiIndices SymmetricLineBasis SymmetricZeroSpace SymmetricCoordinateSplit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CoordinateBasis.
Variable K : fieldType.

(** Source for [symmetric_coordinate_monomial]: Federer 1.9.2,
    p. 42, supporting recursive monomial: in zero variables it is
    the unit; the next variable contributes its indicated power,
    multiplied with the monomial in the remaining variables. *)
Fixpoint symmetric_coordinate_monomial n : symmetric_multi_index n ->
    symmetric_space (coordinate_space K n) :=
  match n as k return symmetric_multi_index k ->
      symmetric_space (coordinate_space K k) with
  | 0 => fun _ => symmetric_unit (coordinate_space K 0)
  | k.+1 => fun a => symmetric_coordinate_join K k
      (tensor_inj (symmetric_line_power K (symmetric_multi_head a))
        (@symmetric_coordinate_monomial k (symmetric_multi_tail a)))
  end.

(** Source for [symmetric_coordinate_monomial_basis]: Federer
    1.9.2, p. 42, monomials indexed by nonnegative integer tuples
    form a homogeneous basis of the whole symmetric algebra.
    The degree is the sum of the entries. This supporting whole-algebra
    assertion yields the printed assertion in each degree. *)
Theorem symmetric_coordinate_monomial_basis n :
  is_graded_basis (symmetric_grading (coordinate_space K n))
    (@symmetric_coordinate_monomial n) (@symmetric_multi_degree n).
Proof.
elim: n => [|n [hb hg]].
- have [hb hg] := zero_space_symmetric_unit_basis (@coordinate_zero K).
  split.
  + exact: (@basis_reindex K (Choice.clone unit _)
      (Choice.clone (symmetric_multi_index 0) _)
      (symmetric_space (coordinate_space K 0))
      (fun _ : unit => symmetric_unit (coordinate_space K 0)) hb
      (fun _ => symmetric_multi_zero 0) (fun _ => tt)
      (fun u => match u with tt => erefl tt end)
      (fun a => esym (symmetric_multi_index_empty a))).
  + move=> a; rewrite /symmetric_multi_degree big_ord0.
    exact: symmetric_unit_homogeneous.
- have [hl hlg] := symmetric_line_graded_basis K.
  have ht := tensor_basisP hl hb.
  have hj := basis_transport (@symmetric_coordinate_joinK K n)
    (@symmetric_coordinate_splitK K n) ht.
  split.
  + apply: (@basis_reindex K
      (Choice.clone (nat * symmetric_multi_index n)%type _)
      (Choice.clone (symmetric_multi_index n.+1) _)
      (symmetric_space (coordinate_space K n.+1))
      (fun ka => symmetric_coordinate_join K n
        (tensor_inj (symmetric_line_power K ka.1)
          (symmetric_coordinate_monomial ka.2))) hj
      (fun ka => symmetric_multi_cons ka.1 ka.2)
      (fun a => (symmetric_multi_head a, symmetric_multi_tail a))).
    * by move=> [k a]; rewrite symmetric_multi_cons_head symmetric_multi_cons_tail.
    * exact: symmetric_multi_head_tail.
  + move=> a; change (homogeneous (symmetric_grading (coordinate_space K n.+1)) (symmetric_multi_degree a)
      (symmetric_coordinate_join K n
        (tensor_inj (symmetric_line_power K (symmetric_multi_head a))
          (symmetric_coordinate_monomial (symmetric_multi_tail a))))).
    have hd : symmetric_multi_degree a =
      (symmetric_multi_head a + symmetric_multi_degree (symmetric_multi_tail a))%N.
      by rewrite -{1}(symmetric_multi_head_tail a) symmetric_multi_degree_cons.
    rewrite hd; apply: (@symmetric_coordinate_join_graded K n).
    exact: tensor_homogeneous_pure (hlg _) (hg _).
Qed.
End CoordinateBasis.
