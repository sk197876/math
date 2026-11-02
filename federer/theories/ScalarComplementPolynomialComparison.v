(** Federer (1969), 3.2.36, p. 273: compare the actual
    finite tube polynomials after grouping their radius degrees. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import PolynomialCoefficientUniqueness PositivePolynomialCoefficientUniqueness
  FinitePolynomialDegreeGrouping EuclideanBallVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_reverse_power_sum]: the coefficient reversal
    implicit in comparing the r^(n-m) terms in Federer 3.2.36,
    p. 273. The existing finite ordinal reversal is an involution;
    the identity is purely finite algebra. *)
Lemma finite_reverse_power_sum (R:realType) N (c:'I_N.+1->R) (r:R):
  \sum_(i:'I_N.+1) c i*r^+(N-i)=
    \sum_(d:'I_N.+1) c (rev_ord d)*r^+d.
Proof.
rewrite (reindex_inj rev_ord_inj).
apply:eq_bigr=>d _; congr (_*r^+_).
change ((N-(N.+1-d.+1))%N=d).
rewrite subSS subKn //.
by have:=ltn_ord d; rewrite ltnS.
Qed.

(** Source for [scalar_complement_polynomial_comparison]: the coefficient
    deduction of the Cartesian intrinsic-volume convolution in Federer
    3.2.36, p. 273. Actual alpha coefficients are strictly positive,
    so the internal finite root-count comparison cancels them after
    regrouping. The conclusion retains all pair indices and every
    natural product degree, including zero and both empty blocks. *)
Theorem scalar_complement_polynomial_comparison (R:realType) m n
    (x:'I_m.+1->R) (y:'I_n.+1->R) (z:'I_(m+n).+1->R):
  (forall r:R,0<r ->
    \sum_(l:'I_(m+n).+1) z l*(euclidean_unit_ball_volume R (m+n-l)*r^+(m+n-l))=
    \sum_(i:'I_m.+1) \sum_(j:'I_n.+1)
      (x i*y j)*(euclidean_unit_ball_volume R ((m-i)+(n-j))*r^+((m-i)+(n-j)))) ->
  forall l:'I_(m+n).+1,z l=\sum_(i:'I_m.+1) \sum_(j:'I_n.+1|(i+j==l)%N) x i*y j.
Proof.
move=>hEqual.
pose N:=(m+n)%N.
pose a (d:'I_N.+1):R:=z (rev_ord d)*euclidean_unit_ball_volume R d.
pose b (d:'I_N.+1):R:=(\sum_(i:'I_m.+1) \sum_(j:'I_n.+1|((m-i)+(n-j)==d)%N) x i*y j)*
  euclidean_unit_ball_volume R d.
have hGrouped r:0<r ->\sum_(d:'I_N.+1) a d*r^+d=\sum_(d:'I_N.+1) b d*r^+d.
  move=>hr; have h:=hEqual r hr.
  have hLeft: \sum_(l:'I_N.+1) z l*(euclidean_unit_ball_volume R (N-l)*r^+(N-l))=
      \sum_(d:'I_N.+1) a d*r^+d.
    under eq_bigr do rewrite mulrA.
    rewrite finite_reverse_power_sum; apply:eq_bigr=>d _.
    have hRev:(N-rev_ord d)%N=d.
      change ((N-(N.+1-d.+1))%N=d); rewrite subSS subKn //.
      by have:=ltn_ord d; rewrite ltnS.
    by rewrite /a hRev.
  rewrite hLeft in h.
  have hRight: \sum_(i:'I_m.+1) \sum_(j:'I_n.+1)
      (x i*y j)*(euclidean_unit_ball_volume R ((m-i)+(n-j))*r^+((m-i)+(n-j)))=
      \sum_(d:'I_N.+1) b d*r^+d.
    under eq_bigr do under eq_bigr do rewrite mulrA.
    rewrite finite_complement_degree_grouping; apply:eq_bigr=>d _; congr (_*r^+d).
    rewrite /b !mulr_suml; apply:eq_bigr=>i _; rewrite mulr_suml.
    apply:eq_bigr=>j /eqP hd; by rewrite hd.
  by rewrite -hRight.
pose c (d:nat):R^o:=a (inord d).
pose e (d:nat):R^o:=b (inord d).
have hNat (r:R):0<r ->\sum_(d<N.+1) r^+d*:c d=\sum_(d<N.+1) r^+d*:e d.
  move=>hr.
  have hLeft: \sum_(d<N.+1) r^+d*:c d=\sum_(d:'I_N.+1) a d*r^+d.
    apply:eq_bigr=>d _; by rewrite /c inord_val mulrC.
  have hRight: \sum_(d<N.+1) r^+d*:e d=\sum_(d:'I_N.+1) b d*r^+d.
    apply:eq_bigr=>d _; by rewrite /e inord_val mulrC.
  rewrite hLeft hRight; exact:hGrouped r hr.
have hCoefficients:=@positive_finite_power_coefficients_unique R R^o N.+1 c e hNat.
move=>l.
have hDegree:(rev_ord l<N.+1)%N:=ltn_ord (rev_ord l).
have h:=hCoefficients (rev_ord l) hDegree.
rewrite /c /e inord_val /a /b rev_ordK in h.
have hAlpha:(euclidean_unit_ball_volume R (rev_ord l)!=0) by rewrite gt_eqF //; exact:(euclidean_unit_ball_volumeE R _).2.
have hCancel:=mulIf hAlpha h.
rewrite hCancel; apply:eq_bigr=>i _; apply:eq_bigl=>j.
have hi:(i<=m)%N by have:=ltn_ord i; rewrite ltnS.
have hj:(j<=n)%N by have:=ltn_ord j; rewrite ltnS.
have hl:(l<=N)%N by have:=ltn_ord l; rewrite ltnS.
change (((m-i)+(n-j)==N.+1-l.+1)%N=(i+j==l)%N).
rewrite subSS (addnBA _ hj) (addnBAC _ hi) -subnDA.
exact:(@eqn_sub2lE N l (i+j) (leq_add hi hj) hl).
Qed.
