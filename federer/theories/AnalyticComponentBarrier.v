(** Federer (1969), 3.4.8(11), p. 333:
    the original analytic barrier is
    Psi(y)=(epsilon squared minus |y| squared)
    times Phi(y) squared. Its actual formula,
    analyticity, positivity and sphere boundary values
    are retained. It is a local
    proof witness, not a new global choice. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormDifferentialUP NormRegularity NormAnalyticUP NormAnalyticLocal NormAnalyticConstant
  NormAnalyticOperations NormAnalyticScalarProducts EuclideanSquaredNormAnalytic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Barrier.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NR:=(fun z:R^o=>`|z|).
Local Notation hNR:=(@scalar_absolute_value_norm R).
Variables (A:set X) (phi:X->R^o) (epsilon:R).

(** Source for [analytic_component_barrier_analytic]:
    the actual Psi is analytic on
    the original domain of Phi,
    3.4.8(11), p. 333. *)
Lemma analytic_component_barrier_analytic:
  @norm_analytic R X R^o NX NR hNX hNR A phi ->
  @norm_analytic R X R^o NX NR hNX hNR A
    (fun y=>(epsilon^+2-(NX y)^+2)*(phi y)^+2).
Proof.
move=>hPhi.
have hOpen:=norm_analytic_domain_open hPhi.
have hClassZero:=norm_class_continuous (norm_analytic_class_all_orders hPhi 0%N).
have hInterior x (hx:A x):norm_domain_interior NX A x.
  exact:(@hClassZero x hx).1.
have hSquared:=@norm_analytic_open_restriction R X R^o NX NR hNX hNR setT A
  (fun y=>(NX y)^+2) (fun _ _=>Logic.I) hInterior (@euclidean_squared_norm_analytic R n).
have hConstant:=@norm_constant_analytic R X R^o NX NR hNX hNR A hInterior (epsilon^+2).
have hDifference:=norm_analytic_subtract hConstant hSquared.
exact:(norm_analytic_scalar_product hDifference (norm_analytic_scalar_power 2%N hPhi)).
Qed.

(** Source for [analytic_component_barrier_positive]:
    Psi is positive on the original
    open ball outside Phi=0,
    3.4.8(11), p. 333. *)
Lemma analytic_component_barrier_positive y:
  0<epsilon ->NX y<epsilon ->phi y<>0 ->
  0<(epsilon^+2-(NX y)^+2)*(phi y)^+2.
Proof.
move=>hE hNorm hPhi.
have hSquared:(NX y)^+2<epsilon^+2.
  by rewrite ltr_sqr ?nnegrE ?inner_norm_nonnegative //;exact:ltW hE.
have hPhiPositive:0<(phi y)^+2.
  rewrite lt_def sqr_ge0 andbT;apply/negP=>hSquareZero.
  apply:hPhi;apply/eqP.
  by move:hSquareZero;rewrite sqrf_eq0.
apply:mulr_gt0;[by rewrite subr_gt0|exact:hPhiPositive].
Qed.

(** Source for [analytic_component_barrier_sphere_zero]:
    the sphere part of the original
    zero boundary condition for Psi,
    3.4.8(11), p. 333. *)
Lemma analytic_component_barrier_sphere_zero y:
  NX y = epsilon ->(epsilon^+2-(NX y)^+2)*(phi y)^+2 = 0.
Proof. by move=>->;rewrite subrr mul0r. Qed.
End Barrier.
