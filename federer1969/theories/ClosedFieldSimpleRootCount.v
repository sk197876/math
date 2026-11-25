(** Federer (1969), 3.4.12, p. 339: an original degree-k
    polynomial with nonvanishing derivative at every root has exactly
    k distinct complex roots. Reuse the proved root-factor degree
    descent and formal derivative rule for a linear root factor. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativePolynomialUP CommutativePolynomialDegreeUP CommutativePolynomialDegreeBounds
  CommutativePolynomialEvaluationUP CommutativePolynomialEvaluationSealed PolynomialLinearRootFactor
  FormalPolynomialDerivativeUP FormalPolynomialDerivativeExistence FormalPolynomialDerivativeLaws
  ClosedFieldPolynomialRoot.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Count.
Variable K:fieldType.
Variable hClosed:GRing.closed_field_axiom [the pzRingType of (K:Type)].
Variable B:comNzRingType.
Variable embed:{rmorphism K->B}.
Variable variable:B.
Variable coefficient:B->nat->K.
Variable hP:is_commutative_polynomial_ring embed variable coefficient.
Local Notation identity:=(GRing.RMorphism.clone K K idfun _).
Local Notation E:=(fun x:K=>@CommutativePolynomialEvaluation.map K B K embed variable coefficient hP identity x).
Local Notation hE:=(fun x:K=>@CommutativePolynomialEvaluation.laws K B K embed variable coefficient hP identity x).

(** Source for [closed_field_original_simple_root_count]: every
    original nonzero degree-k polynomial has exactly k roots when
    each root has nonzero formal derivative, as used for Y_k in
    3.4.12, p. 339. Degree zero remains included. *)
Theorem closed_field_original_simple_root_count:forall d (P DP:B),
  is_polynomial_degree coefficient P d ->is_formal_polynomial_derivative coefficient P DP ->
  (forall x:K,E x P=0 ->E x DP<>0) ->
  exists roots:seq K,uniq roots /\size roots=d /\forall x:K,E x P=0 <->x \in roots.
Proof.
elim=>[|d IH] P DP hDegree hDP hSimple.
- exists [::];split;first by [].
  split;first by [].
  move=>x;split;last by [].
  move=>hRoot;have hValue:=congr1 (E x) (@polynomial_degree_zero_constant K B embed variable coefficient hP P hDegree).
  rewrite (polynomial_evaluation_constants (hE x)) in hValue.
  apply:False_ind;apply:hDegree.1;exact:esym (eq_trans (esym hRoot) hValue).
- have [x hRootAt]:=@closed_field_original_polynomial_root K hClosed B embed variable coefficient hP P d.+1 hDegree (ltn0Sn d).
  have hRoot:E x P=0:=hRootAt (E x) (hE x).
  have [Q hFactor]:=@polynomial_linear_factor_from_root K B embed variable coefficient hP x (E x)
    (polynomial_evaluation_constants (hE x)) (polynomial_evaluation_variable (hE x)) P hRoot.
  have hQDegree:=@polynomial_linear_root_factor_quotient_degree K B embed variable coefficient hP x P Q d hDegree hFactor.
  have [DQ hDQ]:=@formal_polynomial_derivative_exists K B embed variable coefficient hP Q.
  have hFactorLeft:P=(variable-embed x)*Q by rewrite hFactor mulrC.
  have hProductDP:is_formal_polynomial_derivative coefficient ((variable-embed x)*Q) DP by rewrite -hFactorLeft.
  have hAtX:E x (variable-embed x)=0.
    by rewrite rmorphB (polynomial_evaluation_variable (hE x)) (polynomial_evaluation_constants (hE x)) subrr.
  have hQNonzero:E x Q<>0.
    have hValue:=@formal_polynomial_derivative_at_linear_root K B embed variable coefficient hP K (E x)
      x Q DQ DP hDQ hProductDP hAtX.
    by rewrite -hValue;exact:hSimple x hRoot.
  have hDerivativeEqual:DP=Q+(variable-embed x)*DQ.
    exact:(@formal_polynomial_derivative_unique K B embed variable coefficient hP _ _ _ hProductDP
      (@formal_polynomial_derivative_linear_factor K B embed variable coefficient hP x Q DQ hDQ)).
  have hQSimple y (hy:E y Q=0):E y DQ<>0.
    have hPZero:E y P=0 by rewrite hFactor rmorphM hy mul0r.
    move=>hZero;have hNonzero:=hSimple y hPZero.
    apply:hNonzero.
    by rewrite hDerivativeEqual rmorphD rmorphM hy hZero mulr0 addr0.
  have [roots [hUnique [hCount hRoots]]]:=IH Q DQ hQDegree hDQ hQSimple.
  have hNot:x \notin roots.
    apply/negP=>hX;exact:hQNonzero ((hRoots x).2 hX).
  exists (x::roots);split;first by rewrite /= hNot hUnique.
  split;first by rewrite /= hCount.
  move=>y;split.
  + move=>hZero.
    have hProduct:(E y Q)*(y-x)=0.
      move:hZero;rewrite hFactor rmorphM rmorphB (polynomial_evaluation_variable (hE y))
        (polynomial_evaluation_constants (hE y));by [].
    move/eqP:hProduct;rewrite mulf_eq0 subr_eq0=>/orP[/eqP hQRoot|/eqP hYX].
    * rewrite in_cons;apply/orP;right;exact:(hRoots y).1 hQRoot.
    * by rewrite in_cons hYX eqxx.
  + rewrite in_cons=>/orP[/eqP hYX|hY].
    * by rewrite hYX.
    * have hQRoot:=(hRoots y).2 hY.
      by rewrite hFactor rmorphM hQRoot mul0r.
Qed.
End Count.
