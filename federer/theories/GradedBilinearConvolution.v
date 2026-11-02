(** Federer (1969), 3.1.11, p. 222:
    the homogeneous component of a product is
    the finite convolution of its factor components,
    using the graded algebra laws of 1.2.1,
    p. 11. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP Bilinear GradedAlgebra GradedSums.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section ConvolutionComponents.
Variable K : fieldType.
Variable V : lmodType K.
Variable G : grading V.
Variable mu : V->V->V.
Hypothesis hmu : bilinear mu.
Hypothesis hgrade : graded_product G mu.

(** Source for [graded_bilinear_component_convolution]:
    extracting degree n after multiplication
    gives the sum of products with
    degrees n-j and j, supporting the
    general Leibniz formula in Federer 3.1.11,
    p. 222. No associativity
    or commutativity is needed. *)
Theorem graded_bilinear_component_convolution n a b :
  grade G n (mu a b)=\sum_(j<n.+1) mu (grade G (n-j) a) (grade G j b).
Proof.
move:a b; apply: (graded_induction (G:=G)).
- move=>b; rewrite (bil0l hmu) linear0.
  apply: esym; apply: big1=>j _; by rewrite linear0 (bil0l hmu).
- move=>a a' ha ha' b.
  rewrite (bilDl hmu) linearD ha ha' -big_split.
  apply: eq_bigr=>j _; by rewrite linearD (bilDl hmu).
- move=>p a ha; apply: (graded_induction (G:=G)).
  + rewrite (bil0r hmu) linear0.
    apply: esym; apply: big1=>j _; by rewrite linear0 (bil0r hmu).
  + move=>b b' hb hb'.
    rewrite (bilDr hmu) linearD hb hb' -big_split.
    apply: eq_bigr=>j _; by rewrite linearD (bilDr hmu).
  + move=>q b hb.
    rewrite (grade_homogeneous _ (hgrade ha hb)).
    have he j : mu (grade G (n-j) a) (grade G j b)=
        if j==q then mu (grade G (n-j) a) b else 0.
      rewrite (grade_homogeneous _ hb).
      by case:(j==q); rewrite ?(bil0r hmu).
    under eq_bigr do rewrite he.
    rewrite -big_mkcond.
    case:(ltnP q n.+1)=>hq.
    * rewrite (big_pred1 (Ordinal hq)); last by [].
      rewrite (grade_homogeneous _ ha).
      have hqn : (q<=n)%N by move:hq; rewrite ltnS.
      have heq : (n-q==p)%N=(n==p+q)%N.
        apply/eqP/eqP=>e.
        - by rewrite -e (subnK hqn).
        - by rewrite e addnK.
      rewrite heq; by case:(n==p+q)%N; rewrite ?(bil0l hmu).
    * have hne : (n!=p+q)%N.
        apply/eqP=>heq.
        have hh := leq_trans hq (leq_addl p q).
        by rewrite -heq ltnn in hh.
      rewrite (negPf hne); apply: esym; apply: big1=>j /eqP hj.
      by move:(ltn_ord j); rewrite hj ltnNge hq.
Qed.
End ConvolutionComponents.
