(** Federer (1969), 4.1.12, p. 369:
    finite sums of tests with disjoint
    supports retain their common comass and
    exterior-derivative comass bounds. Reuse the
    original test linearity, derivative support
    inclusion and the earlier unique-support sum bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentSpaces CurrentCoefficientNorms CurrentSupportGeometry
  SmoothTestSpaces CurrentFormSupportValues CurrentBoundarySupport CurrentTestExteriorDerivative
  CurrentTestPointValues RealSeminormUniqueSupportSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentTestFiniteDisjointBounds.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation DT d := (@current_test_space R h2 n U hU d).
Local Notation value d := (@current_test_value R h2 n U hU d).
Local Notation N d := (@current_form_comass R h2 n d).
Local Notation hN d := (@current_form_comass_real_norm R h2 n d).
Local Notation hE d := (@current_smooth_space_laws R h2 n U hU d).
Local Notation support d := (@current_test_support R h2 n d U hU).
Local Notation d := (@current_test_exterior_derivative R h2 n m U hU).
Variable I:finType.
Variable f:I->DT m.

(** Source for [current_test_finite_disjoint_comass_bounds]:
    one common bound on every summand
    and its actual exterior derivative is
    retained by the finite disjoint sum.
    This proves the mechanism behind both
    original psi_m bounds in Federer
    4.1.12, p. 369. *)
Theorem current_test_finite_disjoint_comass_bounds a b:
  0<=a->0<=b->
  (forall x,U x->forall i j,support m (f i) x->support m (f j) x->i=j)->
  (forall i x,U x->N m (value m (f i) x)<=a)->
  (forall i x,U x->N m.+1 (value m.+1 (d (f i)) x)<=b)->
  forall x,U x->N m (value m (\sum_i f i) x)<=a /\
    N m.+1 (value m.+1 (d (\sum_i f i)) x)<=b.
Proof.
move=>ha hb hUnique hBound hDBound x hx.
pose P (i:I):bool:=asbool (support m (f i) x).
have hPUnique i j:P i->P j->i=j.
  move=>/asboolP hi /asboolP hj;exact:hUnique x hx i j hi hj.
have hNotSupport i:~~P i->~support m (f i) x.
  move=>hi hSupport.
  have hP:P i by apply/asboolP.
  by move:hi;rewrite hP.
have hOff i:~~P i->value m (f i) x=0.
  move=>hi;exact:(@current_form_value_outside_support R h2 n m U hU
    (smooth_test_inclusion (hE m) (f i)) x hx (hNotSupport i hi)).
have hDOff i:~~P i->value m.+1 (d (f i)) x=0.
  move=>hi.
  have hNo:~support m.+1 (d (f i)) x.
    move=>hSupport;apply:(hNotSupport i hi).
    exact:(@current_test_exterior_support_subset R h2 n m U hU (f i) x hSupport).
  exact:(@current_form_value_outside_support R h2 n m.+1 U hU
    (smooth_test_inclusion (hE m.+1) (d (f i))) x hx hNo).
split.
- rewrite current_test_finite_sum_value.
  exact:(@real_seminorm_unique_support_sum_bound R _ (N m) (hN m).1 I P
    (fun i=>value m (f i) x) a ha (fun i=>hBound i x hx) hOff hPUnique).
- rewrite (linear_sum d) current_test_finite_sum_value.
  exact:(@real_seminorm_unique_support_sum_bound R _ (N m.+1) (hN m.+1).1 I P
    (fun i=>value m.+1 (d (f i)) x) b hb (fun i=>hDBound i x hx) hDOff hPUnique).
Qed.
End CurrentTestFiniteDisjointBounds.
