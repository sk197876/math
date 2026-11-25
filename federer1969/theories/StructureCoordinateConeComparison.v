(** Federer (1969), 3.3.4, p. 289: finite
    coordinate-square comparisons behind the two actual
    cone inclusions. These elementary scalar statements
    keep the strict inequalities and the positive
    codimension explicit. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals ring lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [structure_coordinate_square_below_sum]:
    one of the nonnegative normal-coordinate squares
    is bounded by their full sum, supporting the
    first cone inclusion in Federer 3.3.4, p. 289. *)
Lemma structure_coordinate_square_below_sum (R:realType) k (b:'I_k->R) j:
  (b j)^+2<=\sum_i (b i)^+2.
Proof.
rewrite (bigD1 j) //= lerDl.
apply:sumr_ge0=>i _; exact:sqr_ge0.
Qed.

(** Source for [structure_coordinate_cone_lower]: the
    inclusion of the union of I_j(r,g,s) in
    A intersect X(0,r,v(g),s), Federer 3.3.4,
    p. 289, at the exact square-sum level. *)
Lemma structure_coordinate_cone_lower (R:realType) k (b:'I_k->R) (a c:R):
  (exists j,c*a<(b j)^+2) ->c*a<\sum_i (b i)^+2.
Proof.
move=>[j hj]; exact:(lt_le_trans hj (structure_coordinate_square_below_sum b j)).
Qed.

(** Source for [structure_coordinate_square_large]: at
    least one normal-coordinate square exceeds the
    mean threshold, supporting the second cone inclusion
    of Federer 3.3.4, p. 289. No weak inequality
    replaces the original strict comparison. *)
Lemma structure_coordinate_square_large (R:realType) k (b:'I_k->R) (a:R):
  k%:R*a<\sum_i (b i)^+2 ->exists j,a<(b j)^+2.
Proof.
move=>hSum; apply:contrapT=>hNo.
have hEach j:(b j)^+2<=a.
  rewrite leNgt; apply/negP=>hj; apply:hNo; by exists j.
have hBound:(\sum_i (b i)^+2)<=k%:R*a.
  have h:(\sum_i (b i)^+2)<=(\sum_(i<k) a).
    apply:ler_sum=>i _; exact:hEach.
  rewrite sumr_const cardT size_enum_ord -mulr_natl in h.
  exact:h.
by have:=lt_le_trans hSum hBound; rewrite ltxx.
Qed.

(** Source for [structure_coordinate_cone_upper]: the
    second union inclusion in Federer 3.3.4, p. 289,
    using the exact printed aperture coefficient relation
    k*c_u=c_s. The sum and each original coordinate
    remain literal, rather than supplied comparison costs. *)
Lemma structure_coordinate_cone_upper (R:realType) k (b:'I_k->R) (a c u:R):
  k%:R*u=c ->c*a<\sum_i (b i)^+2 ->exists j,u*a<(b j)^+2.
Proof.
move=>hCoeff hSum; apply:structure_coordinate_square_large.
by rewrite mulrA hCoeff.
Qed.
