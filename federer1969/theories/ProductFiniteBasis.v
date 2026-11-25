(** Federer (1969), 1.7.11, p. 36: finite dimension of
    S times T and the elementary product basis. The book then
    replaces common pairs by normalised diagonal and antidiagonal
    vectors. Source context: ProductInnerUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ProductLinearMaps LinearBasis FiniteBasisCriterion
  FiniteBasisComparison FiniteIndependence FiniteSpans FiniteDualDimension
  Annihilator Hom ConcatenatedFamilies IndependentConcatenation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Basis.
Variable R : fieldType.
Variables V W : lmodType R.
Variables n m : nat.
Variables (e : 'I_n -> V) (f : 'I_m -> W).
Hypotheses (he : is_basis e) (hf : is_basis f).
Local Notation P := (GRing.Lmodule.clone R (V * W)%type _).

(** Source for [cartesian_basis]: Federer 1.7.11, p. 36,
    supporting basis of the Cartesian product formed by the first
    factor's basis vectors paired with zero and conversely. *)
Definition cartesian_basis : 'I_(n+m) -> P := concatenate_family
  (fun i => @product_left R V W (e i)) (fun j => @product_right R V W (f j)).

(** Source for [cartesian_basisP]: Federer 1.7.11, p. 36,
    supporting fact that the Cartesian product has dimension equal
    to the sum of the factor dimensions, including either empty basis. *)
Theorem cartesian_basisP : is_basis cartesian_basis.
Proof.
apply: finite_basis_criterion.
- apply: disjoint_concatenation_independent.
  + apply: finite_independent_map (finite_basis_independent he).
    move=> x y h; exact (congr1 fst h).
  + apply: finite_independent_map (finite_basis_independent hf).
    move=> x y h; exact (congr1 snd h).
  + move=> x [a ha] [b hb].
    have hfirst := congr1 (@product_first R V W) hb.
    have hsecond := congr1 (@product_second R V W) ha.
    rewrite linear_sum in hfirst.
    rewrite linear_sum in hsecond.
    have hx : @product_first R V W x = 0.
      rewrite hfirst; apply: big1 => i _.
      by rewrite linearZ /product_right /product_first /= scaler0.
    have hy : @product_second R V W x = 0.
      rewrite hsecond; apply: big1 => i _.
      by rewrite linearZ /product_left /product_second /= scaler0.
    clear ha hb hfirst hsecond.
    case: x hx hy => x y /= -> ->; by [].
- move=> [x y]; exists (concatenate_family (fun i => dual_basis he i x) (fun j => dual_basis hf j y)).
  rewrite /cartesian_basis concatenate_family_combination.
  transitivity (@product_left R V W x + @product_right R V W y).
  + change ((x,y) = (x+0,0+y)); by rewrite addr0 add0r.
  + congr (_ + _).
    * rewrite {1}(basis_vector_expansion he x) linear_sum.
      apply: eq_bigr => i _; exact: linearZ.
    * rewrite {1}(basis_vector_expansion hf y) linear_sum.
      apply: eq_bigr => i _; exact: linearZ.
Qed.
End Basis.
